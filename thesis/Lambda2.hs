{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module Lambda2

where

import Prelude hiding (abs)
import Control.Monad.State (State, execState, modify, gets)
import Text.PrettyPrint 
import Data.List (intersperse, (\\), union, nub, delete, sort)
import Data.Maybe (fromMaybe, isJust)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Compiler.Hoopl hiding (addTop)

{-

The lambda-calculus with cases and algebraic data types. Expressions
in the language include:

  expr ::= \x {fvs}. e  -- abstraction w/ free variables annotated
       |   e1 e2   -- application
       |   v       -- variables
       |   case e1 of [alt1, ..., altN] -- Case discrimination
       |   C e1 ... eN -- Constructor 

  alt ::= C v1 ... vN -> e

A program consists of multiple, possibly recursive, top-level
definitions:

  def ::= f = expr

  prog ::= def1
           ...
           defN
-}

type Name = String
type Var = String
type Constructor = String

data Expr = Abs Var Free Expr
          | App Expr Expr
          | Var Var
          | Case Expr [Alt Expr]
          | Constr Constructor [Expr]
  deriving (Show, Eq)

data Alt e = Alt Constructor [Name] e
  deriving (Show, Eq)

type Free = [Name] 
type Def = (Name, Expr)
type Prog = [Def]

-- | Collect free variables from Abs terms on 
-- the lambda-calculus expression.
collectFree :: Expr -> [Name]
collectFree (Abs _ vs _) = vs
collectFree (App e1 e2) = collectFree e1 ++ collectFree e2
collectFree (Var v) = [] 
collectFree (Case e alts) = collectFree e ++ concatMap (\(Alt _ _ e) -> collectFree e) alts
collectFree (Constr _ exprs) = concatMap collectFree exprs

{-

Our monadic language:

  
  bodyM ::= do 
    stmtM1; 
    ... ; 
    stmtMN; 
    tailM

  stmtM ::= v <- tailM
    | case v of [alt1, ..., altN]
    | tailM

  tailM ::= return v
    | v1 @ v2         -- Call an unknown function.
    | f(v1, ..., v)  -- Goto a known block.
    | closure f {v1, ..., vN} -- Create closure pointing to a function.

  alt ::= C v1 ... vN -> call f(u1, ..., uM)

  defM ::= f {v1, ..., vN} v = bodyM -- ``f'' stands for the name of the function.

  progM :: defM1
           ...
           defMN
-}

type Dest = (Name, Label)

data StmtM e x where
  -- | Entry point to a block.
  BlockEntry :: Name -- Name of the block
    -> Label    -- Label of the entry point.
    -> [Name] -- arguments
    -> StmtM C O

  -- | Entry point to a closure-capturing block.
  CloEntry :: Name -- Name of the block
    -> Label    -- Label of the entry point.
    -> [Name]   -- Variables in closure
    -> Name     -- argument
    -> StmtM C O
  
  Bind :: Name      -- Name of variable that will be bound.
    -> TailM    -- Expression that computes the value we want.
    -> StmtM O O    -- Open/open since bind does not end an expression
  
  CaseM :: Name      -- Variable to inspect
      -> [Alt TailM] -- Case arms
      -> StmtM O C
      
  Done :: TailM  -- Finish a block.
      -> StmtM O C

-- | TailM concludes a list of statements. Each
-- block ends with a TailM except when CaseM ends
-- the blocks.
data TailM = Return Name 
  | Enter Name     -- Variable holding the closure.
    Name         -- Argument to the function.
  | Closure Dest   -- The variable holding the address of the function.
    [Name]               -- List of captured free variables.
  | Goto Dest         -- Address of the block
    [Name]       -- Arguments/live variables used in the
                         -- block. Uses Maybe so arguments can be
                         -- filled after live variable analysis of
                         -- the block
  | ConstrM Constructor  -- Constructor name.
      [Name]             -- Only variables allowed as arguments to constructor.
  deriving (Eq, Show)

-- -- | Collect free variables in a program.
-- freeM :: [Name] -> ProgM O C -> [Name] 
-- freeM tops prog = 
--   let fvs = nub . filter (not . null) . concat . maybeGraph [[]] freeB
--   in (fvs prog) \\ tops

-- -- | Free variables in a block.
-- freeB :: Block StmtM x e -> [Name] 
-- freeB b = maybeC id useDef e mids
--   where
--     (e, bs, x) = blockToNodeList' b
--     mids = foldr useDef (maybeC id useDef x [])  bs
         
--     useDef                    :: StmtM e x -> [Name] -> [Name] 
--     useDef (BlockEntry _ _ _) live = live
--     useDef (CloEntry _ _ _ _) live = live
--     useDef (Bind v t) live    = delete v live ++ useTail t
--     useDef (CaseM v alts) _   = v : concatMap (\(Alt _ vs t) -> useTail t \\ vs) alts
--     useDef (Done t) live      = live ++ useTail t

--     useTail                :: TailM -> [Name] 
--     useTail (Return v)     = [v]
--     useTail (Enter v1 v2)  = [v1, v2]
--     useTail (Closure _ vs) = vs
--     useTail (Goto _ vs)    = vs
--     useTail (ConstrM _ vs) = vs

-- Compiling from lambda-calculus to the monadic language.

compileM :: [Name] -> Def -> ProgM C C
compileM tops def = compG $ foldr compDef initial $ addFVs tops [def]
  where
    compDef p = execState (uncurry newDefn p)
    initial = C 0 emptyClosedGraph tops
    -- | Creates a new function definition
    -- using the arguments given and adds it
    -- to the control flow graph.    
    newDefn :: Name -> Expr -> CompM ()
    newDefn name (Abs v fvs b) = do
      prog <- compileStmtM b (return . mkLast . Done)
      cloDefn name v fvs prog >> return ()
    newDefn name body = do
      prog <- compileStmtM body (return . mkLast . Done)
      blockDefn name [] prog >> return ()

compileStmtM :: Expr 
  -> (TailM -> CompM (ProgM O C))
  -> CompM (ProgM O C)

compileStmtM (Var v) ctx 
  = ctx (Return v)

compileStmtM (App e1 e2) ctx 
  = compVarM e1 $ \f ->
    compVarM e2 $ \g ->
      ctx (Enter f g)

compileStmtM (Case e alts) ctx = do
  r <- fresh "result"
  f <- ctx (Return r) >>= callDefn "caseJoin" 
  let compAlt (Alt cons vs body) = do
        body' <- compileStmtM body (mkBind r f) >>= callDefn ("altBody" ++ cons)
        return (Alt cons vs body')
  altsM <- mapM compAlt alts
  compVarM e $ \v -> return (mkLast (CaseM v altsM))
  where
    callDefn :: String -> ProgM O C -> CompM TailM
    callDefn name body = do 
      f <- newTop name
      ts <- gets compT
      dest <- blockDefn f [] body
      return (Goto dest [])

compileStmtM (Abs v fvs b) ctx = do
  f <- do
    prog <- compileStmtM b (return . mkLast . Done)
    name <- newTop "absBody"
    cloDefn name v fvs prog 
  ctx (Closure f fvs)

compileStmtM (Constr cons exprs) ctx = 
  let compExpr vs [] = ctx (ConstrM cons (reverse vs))
      compExpr vs (e:es) = compVarM e $ \v -> 
                           compExpr (v:vs) es
  in compExpr [] exprs


mkBind r f t = return (mkMiddle (Bind r t) <*> mkLast (Done f))
      
compVarM :: Expr 
  -> (Name -> CompM (ProgM O C))
  -> CompM (ProgM O C)
compVarM (Var v) ctx = ctx v
compVarM e ctx       = compileStmtM e $ \t -> do
  v <- fresh "v"
  rest <- ctx v
  return (mkMiddle (v `Bind` t) <*> rest)

-- Compiler State

-- | Compiler state. 
data CompS = C { compI :: Int -- ^ counter for fresh variables
               , compG :: (ProgM C C) -- ^ Program control-flow graph.
               , compT :: [Name] } -- ^ top-level function names.
               
type ProgM = Graph StmtM
type CompM = State CompS

-- | Add a name to the list of top-level functions.
addTop :: Name -> CompM ()
addTop name = modify (\s@(C { compT }) -> s { compT = name : compT })

-- | Make a new top-level function name, based on the
-- prefix given.
newTop :: Name -> CompM Name
newTop name = do
  f <- fresh name
  addTop f
  return f

-- | Add a new block.
blockDefn :: Name -> [Name] -> ProgM O C -> CompM Dest
blockDefn name args progM = withNewLabel $ \l -> do
  addProg (mkFirst (BlockEntry name l args) <*> progM)
  return (name, l)
  
-- | Add a new closure-capturing block.
cloDefn :: Name -> Name -> [Name] -> ProgM O C -> CompM Dest
cloDefn name arg clos progM 
  | not (isCapture progM) = withNewLabel $ \l -> do
                          let args = clos ++ [arg]
                          dest <- blockDefn ("block" ++ name) args progM
                          addProg (mkFirst (CloEntry name l clos arg) <*>
                                   mkLast (Done (Goto dest args)))
                          return (name, l)
  | otherwise = withNewLabel $ \l -> do
                  addProg (mkFirst (CloEntry name l clos arg) <*> progM)
                  return (name, l)
  where
    isCapture :: ProgM O C -> Bool
    isCapture (GMany (JustO block) _ _ ) = 
      case blockToNodeList' block of
        (_, [], (JustC (Done (Closure _ _)))) -> True
        _ -> False

-- | Add a program (C C block) to the list of blocks
-- maintained by the monad.
addProg :: ProgM C C -> CompM ()
addProg block = modify (\s@(C { compG }) -> s { compG = block |*><*| compG })

-- | Do something with a new label.
withNewLabel :: UniqueMonad m => (Label -> m a) -> m a
withNewLabel f = freshLabel >>= f
  
-- | Create a fresh variable with the given
-- prefix.
fresh :: String -> CompM String
fresh prefix = do
  i <- gets compI
  modify (\s@(C { compI }) -> s { compI = compI + 1})
  return (prefix ++ show i)

-- | Create a new unique value; used in the
-- instance declaration for (UniqueMonad CompM).
freshVal :: CompM Unique
freshVal = do
  i <- gets compI
  modify (\s@(C { compI }) -> s { compI = compI + 1})
  return (intToUnique i)

instance UniqueMonad CompM where
  freshUnique = freshVal

instance NonLocal StmtM where
  entryLabel (BlockEntry _ l _) = l
  entryLabel (CloEntry _ l _ _) = l
  successors = stmtSuccessors
                        
stmtSuccessors :: StmtM e C -> [Label]
stmtSuccessors (CaseM _ alts) = concatMap (\(Alt _ _ t) -> tailDest t) alts
stmtSuccessors (Done t) = tailDest t

tailDest :: TailM -> [Label]
tailDest (Closure (_, l) _) = [l]
tailDest (Goto (_, l) _) = [l]
tailDest _ = []

-- | Annotate lambda-calculus programs with free variables.
addFVs :: [Name] -> Prog -> Prog
addFVs tops ps = map (\(name, body) -> (name, snd $ annotate body)) ps
  where
    -- Add free variables to each lambda.
    annotate :: Expr -> (Free, Expr)
    annotate (Abs v _ expr)   
      = let (fvs, expr') = annotate expr
            fvs'         = delete v (nub fvs)
        in (fvs', Abs v fvs' expr')
    annotate (App e1 e2)      
      = let (fvs1, e1') = annotate e1
            (fvs2, e2') = annotate e2
        in (fvs1 ++ fvs2, App e1' e2')
    annotate e@(Var v)  
      | v `elem` tops = ([], e)
      | otherwise = ([v], e)
    annotate (Case e alts)    
      = let (fvs1, e')    = annotate e
            (fvs2, alts') = unzip $ map annotateAlt alts
        in (fvs1 ++ concat fvs2, Case e' alts')
    annotate (Constr c exprs) 
      = let (fvs1, exprs') = unzip $ map annotate exprs
        in (concat fvs1, Constr c exprs')
    annotateAlt (Alt c ns e) 
      = let (fvs, e') = annotate e
        in (fvs \\ ns, Alt c ns e')

-- Printing lambda-calculus terms

printDef :: Def -> Doc
printDef (name, body) = hang (text name <+> text "=") 2 (printExpr body) 

printExpr :: Expr -> Doc
printExpr (Abs var fvs e) = text "\\" <> text var <+> braces (hsep (punctuate comma (texts fvs))) <>  text "." <+> printExpr e
printExpr (App e1 e2) = printVar e1 <+> printVar e2
printExpr (Var v) = text v
printExpr (Case e alts) = hang (text "case" <+> printExpr e <+> text "of") 2 (vcat' . map printAlt $ alts)
  where
    printAlt (Alt cons vs e) = text cons <+> (hsep (texts vs)) <+> text "->" <+> printExpr e
printExpr (Constr cons exprs) = text cons <+> (hsep . map printVar $ exprs)

printVar (Var v) = text v
printVar e = parens (printExpr e)

-- Pretty printing programs
printProgM :: ProgM C C -> Doc
printProgM = vcat' . maybeGraph empty printBlockM

printBlockM = p . blockToNodeList'
  where p (e, bs, x) = hang (maybeC empty printStmtM e) 2
                       (vcat' (map printStmtM bs) $+$
                        maybeC empty printStmtM x)
 
printStmtM :: StmtM e x -> Doc
printStmtM (Bind n b) = text n <+> text "<-" <+> nest 2 (printTailM b)
printStmtM (BlockEntry f l args) = text (show l ++ "_" ++ f) <+> 
                                  parens (commaSep text args) <> text ":" 
printStmtM (CloEntry f l clos arg) = text (show l ++ "_" ++ f) <+> 
                                  parens (text arg) <+> braces (commaSep text clos) <> text ":" 
printStmtM (CaseM v alts) = hang (text "case" <+> text v <+> text "of") 2 (vcat' $ map printAlt alts)
  where
    printAlt (Alt cons vs tailM) = text cons <+> hsep (texts vs) <+> text "->" <+> printTailM tailM
printStmtM (Done t) = printTailM t

printTailM :: TailM -> Doc
printTailM (Return n) = text "return" <+> text n
printTailM (Enter f a) = text f <+> text "@" <+> text a
printTailM (Closure dest vs) = text "closure" <+> printDest dest <+> braces (commaSep text vs)
printTailM (Goto dest vs) = printDest dest <> parens (commaSep text vs)
printTailM (ConstrM cons vs) = text cons <+> (hsep $ texts vs)

printDest :: Dest -> Doc
printDest (name, l) = text (show l ++ "_" ++ name)

-- Pretty-printing utilities

vcat' :: [Doc] -> Doc
vcat' = foldl ($+$) empty

commaSep = punctuated comma 
spaced = punctuated space 
texts = map text

punctuated :: Doc -> (a -> Doc) -> [a] -> Doc
punctuated sep f = hcat . punctuate sep . map f

-- | Use the printer given when j is a Just value,
-- otherwise use the empty document.
maybeP :: (a -> Doc) -> Maybe a -> Doc
maybeP j = maybe empty j 

-- Hoopl utilities

maybeC :: a -> (n -> a) -> MaybeC e1 n -> a
maybeC _ f (JustC e) = f e
maybeC def f _ = def 

maybeO :: a -> (n -> a) -> MaybeO e1 n -> a
maybeO def f (JustO b) = f b
maybeO def f _ = def

{-
 
The below definition will not compile with maybeGraph2. I think it maybeGraph2 is too
polymorphic - I don't know if I can ever write a function that will satisfy it.

printWithLive2 :: (Def, ProgM C C) -> Doc
printWithLive2 (def, comp) = 
  let live = findLive [] comp
      printLive :: FactBase LiveFact -> Block StmtM C x -> Doc
      printLive live p = 
        let label = fst (getEntryLabel p)
            vars = maybe [] Set.elems (lookupFact label live)
            livePrefix = if null vars
                         then text "[nothing live]"
                         else brackets (commaSep text vars) 
        in livePrefix <+> printBlockM p 
  in printDef def $+$
     vcat' (maybeGraph2 empty (printLive live) comp)

maybeGraph2 :: b -> (forall e1 x1. block node e1 x1 -> b) -> Graph' block node e2 x2 -> [b]
maybeGraph2 b _ GNil = []
maybeGraph2 b f (GUnit block) = [f block]
maybeGraph2 b f (GMany entry middles exit) = maybeO b f entry :
                                        (map f . mapElems $ middles) ++
                                        [maybeO b f exit]

-}
maybeGraph :: b -> (block node C C -> b) -> Graph' block node C C -> [b]
maybeGraph b f (GMany _ middles _) = map f . mapElems $ middles

-- | Get all the labels at entry points in 
-- the program.
entryPoints :: ProgM C C -> [(Label, StmtM C O)]
entryPoints (GMany _ blocks _) = map getEntryLabel (mapElems blocks)

allBlocks :: ProgM C C -> [(Label, Block StmtM C C)]
allBlocks (GMany _ blocks _) = map (\b -> (fst (getEntryLabel b), b)) (mapElems blocks)

blockTail :: Block StmtM C C -> ProgM O C
blockTail b = case blockToNodeList' b of
                (JustC _, mid, JustC end) -> mkMiddles mid <*> mkLast end

getEntryLabel :: Block StmtM C x -> (Label, StmtM C O)
getEntryLabel block = case blockToNodeList' block of
  (JustC e@(BlockEntry _ l _), _, _) -> (l, e)
  (JustC e@(CloEntry _ l _ _), _, _) -> (l, e)

printFB :: (IsMap map) => ((KeyOf map, a) -> Doc) -> map a -> Doc
printFB p = vcat . map p . mapToList

done :: FuelMonad m => Maybe TailM -> m (Maybe (ProgM O C))
done = return . maybe Nothing (Just . mkLast . Done)

bind :: FuelMonad m => Name -> Maybe TailM -> m (Maybe (ProgM O O))
bind v = return . maybe Nothing (Just . mkMiddle . Bind v)

_case :: FuelMonad m => Name -> (Alt TailM -> Maybe (Alt TailM)) -> [Alt TailM] -> m (Maybe (ProgM O C))
_case v f alts  
  | any isJust alts' = return $ Just $ mkLast $ CaseM v (zipWith altZip alts alts')
  | otherwise = return $ Nothing
  where
    alts' = map f alts
    altZip _ (Just a) = a
    altZip a _ = a
    
-- Determining liveness in StmtM

type LiveFact = Set Name

-- | Used to apply different rewriters which all require 
-- live variable analysis.
usingLive :: (forall m. FuelMonad m => (BwdRewrite m StmtM LiveFact)) -- ^ Rewrite to use
          -> [Name] -- ^ Top-level variables
          -> ProgM C C -- ^ Program to rewrite
          -> (ProgM C C, FactBase LiveFact) -- Results
usingLive rewriter tops body = runSimpleUniqueMonad $ runWithFuel infiniteFuel findLive' 
  where
    -- | Finds the live variables in the program
    -- given. 
    findLive' :: SimpleFuelMonad (ProgM C C, FactBase LiveFact)
    findLive' = do
      (p, f, _) <- analyzeAndRewriteBwd bwd (JustC (map fst (entryPoints body))) body mapEmpty
      return (p, f)
    bwd = BwdPass { bp_lattice = liveLattice
                  , bp_transfer = liveTransfer (Set.fromList tops)
                  , bp_rewrite = rewriter } 

-- | Initial setup for liveness analysis.
liveLattice :: DataflowLattice LiveFact
liveLattice = DataflowLattice { fact_name = "Liveness"
                              , fact_bot = Set.empty
                              , fact_join = extend }
  where
    extend _ (OldFact old) (NewFact new) = (changeIf (not (Set.null (Set.difference new old)))
                                           , new)

-- | Transfer liveness backwards across nodes.                                         
liveTransfer :: Set Name -> BwdTransfer StmtM LiveFact
liveTransfer tops = mkBTransfer live
  where
    live :: StmtM e x -> Fact x LiveFact -> LiveFact
    live (BlockEntry _ _ _) f = woTops f 
    live (CloEntry _ _ _ _) f = woTops f
    live (Bind v t) f = woTops (Set.delete v f  `Set.union` tailVars mapEmpty t )
    live (CaseM v alts) f = woTops (Set.insert v (Set.unions (map (setAlt f) alts)))
    live (Done t) f = woTops (tailVars f t)

    woTops :: LiveFact -> LiveFact
    woTops live = live `Set.difference` tops
    
    setAlt :: FactBase LiveFact -> Alt TailM -> Set Name
    setAlt f (Alt _ ns e) = Set.difference (tailVars f e) (Set.fromList ns)

    -- | Returns variables used in a tail expression.
    tailVars :: FactBase LiveFact -> TailM -> Set Name
    tailVars f (Closure (_, l) vs) = Set.fromList vs 
    tailVars f (Goto (_, l) vs) = Set.fromList vs
    tailVars _ (Enter v1 v2) = Set.fromList [v1, v2]
    tailVars _ (ConstrM _ vs) = Set.fromList vs
    tailVars _ (Return n) = Set.singleton n

-- | Retrieve a fact or the empty set
liveFact :: FactBase LiveFact -> Label -> Set Name
liveFact f l = fromMaybe Set.empty $ lookupFact l f

-- | Returns live variables associated with each
-- label in the program.
findLive :: [Name] -- ^ Top-level variables
         -> ProgM C C -- ^ Program to analyze
         -> FactBase LiveFact -- Results
findLive tops = snd . usingLive noBwdRewrite tops 

-- | Adds live variables to Goto and BlockEntry instructions. Not
-- filled in by the compiler - added in this pass instead.
addLiveRewriter :: FuelMonad m => BwdRewrite m StmtM LiveFact
addLiveRewriter = mkBRewrite rewrite
  where
    rewrite :: FuelMonad m => forall e x. StmtM e x -> Fact x LiveFact -> m (Maybe (ProgM e x))
    rewrite (Done t) f = done (rewriteTail f t)
    rewrite (BlockEntry n l args) live 
      | live /= Set.fromList args = blockEntry n l (sort (Set.toList live))
    rewrite (CaseM n alts) f = _case n (rewriteAlt f) alts
    -- Why do I not need to worry about Bind here? What shows I can't have a 
    -- Goto in the tail?
    rewrite _ _ = return Nothing
    
    rewriteAlt f (Alt c ns t) = maybe Nothing (Just . Alt c ns) (rewriteTail f t)

    rewriteTail :: FactBase LiveFact -> TailM -> Maybe TailM
    rewriteTail f (Goto (n, l) vs) = 
      case l `mapLookup` f of
        Just vs' 
          | vs' /= Set.fromList vs -> Just (Goto (n,l) (sort (Set.toList vs')))
        _ -> Nothing
    rewriteTail _ _ = Nothing
    
    blockEntry :: FuelMonad m => Name -> Label -> [Name] -> m (Maybe (ProgM C O))
    blockEntry n l args = return $ Just $ mkFirst $ BlockEntry n l args

-- | From mon5.lhs
--
--   Compile-time garbage collection:
--    Bind v a c           ==> c         if a is an allocator and
--                                          v doesn't appear in c
--
-- deadRewriter implemented similary, where "safeTail" determines if the
-- expression on the right of the array can be elminiated safely.
-- 
deadRewriter :: FuelMonad m => BwdRewrite m StmtM LiveFact
deadRewriter = mkBRewrite rewrite
  where
    rewrite :: FuelMonad m => forall e x. StmtM e x -> Fact x LiveFact -> m (Maybe (ProgM e x))
    rewrite (Bind v t) f 
            | safeTail t && not (v `Set.member` f) = return (Just emptyGraph)
    rewrite _ _ = return Nothing

    -- Indicates when it is OK to eliminate a tail instruction in a monadic
    -- expression.
    safeTail :: TailM -> Bool
    safeTail (Return _) = True
    safeTail (Closure _ _) = True
    safeTail (ConstrM _ _) = True
    safeTail _ = False

-- | printing live facts
printLiveFacts :: FactBase LiveFact -> Doc
printLiveFacts = printFB printFact
  where
    printFact :: (Label, Set Name) -> Doc
    printFact (l, ns) = text (show l) <> text ":" <+> commaSep text (Set.elems ns)

-- From mon5.lhs
--     v <- return w; c  ==>  c       if v == w
--                       ==> [w/v] c  otherwise
--     Bind v (Return w) c  ==> c    if v==w
--                       c  ==> [w/v] c  otherwise

-- | Substitute the key for the value.
type BindFact = Map Name Name

bindSubst :: ProgM C C -> ProgM C C
bindSubst body = runSimpleUniqueMonad $ runWithFuel infiniteFuel bindSubst'
  where
    bindSubst' :: SimpleFuelMonad (ProgM C C)
    bindSubst' = do
      let entries = map fst (entryPoints body)
          initial = mapFromList (zip entries (repeat Map.empty))
      (p, _, _) <- analyzeAndRewriteFwd fwd (JustC entries) body initial
      return p
    fwd = FwdPass { fp_lattice = bindSubstLattice
                  , fp_transfer = bindSubstTransfer
                  , fp_rewrite = bindSubstRewrite }

bindSubstLattice :: DataflowLattice BindFact
bindSubstLattice = DataflowLattice { fact_name = "Bind/Return substitution"
                                   , fact_bot = Map.empty
                                   , fact_join = extend }
  where
    extend _ (OldFact old) (NewFact new) = (changeIf (old /= new)
                                           , new)

bindSubstTransfer :: FwdTransfer StmtM BindFact
bindSubstTransfer = mkFTransfer fw
  where
    fw :: StmtM e x -> BindFact -> Fact x BindFact
    fw (Bind v (Return w)) m = Map.insert v w m 
    fw (Bind v _) m = Map.delete v m 
    fw (BlockEntry _ _ _) m = m
    fw (CloEntry _ _ _ _) m = m
    fw (CaseM _ alts) m = 
      mkFactBase bindSubstLattice []
    fw (Done t) m = 
      mkFactBase bindSubstLattice []


bindSubstRewrite :: FuelMonad m => FwdRewrite m StmtM BindFact
bindSubstRewrite = iterFwdRw (mkFRewrite rewrite) -- deep rewriting used
                                                   -- so all possible
                                                   -- substitutions occur
  where
    rewrite :: FuelMonad m => forall e x. StmtM e x -> BindFact -> m (Maybe (ProgM e x))
    rewrite (Bind v t) f = bind v (rewriteTail f t)
    rewrite (CaseM v alts) f 
        | Map.member v f = _case (f ! v) Just alts
        | otherwise = _case v (replaceAlt f) alts
        where
          replaceAlt f (Alt c ns t) 
            | anyIn f ns = Just $ Alt c (map (replace f) ns) t
            | otherwise = maybe Nothing (Just . Alt c ns) (rewriteTail f t)
    rewrite (Done t) f = done (rewriteTail f t)
    rewrite _ _ = return Nothing

    rewriteTail :: BindFact -> TailM -> Maybe TailM
    rewriteTail f (Return v) 
      | Map.member v f = Just $ Return (f ! v)
    rewriteTail f (Enter v w)
      | Map.member v f = Just $ Enter (f ! v) w
      | Map.member w f = Just $ Enter v (f ! w)
    rewriteTail f (Closure d ns) 
      | anyIn f ns = Just $ Closure d (map (replace f) ns)
    rewriteTail f (Goto d ns) 
      | anyIn f ns = Just $ Goto d (map (replace f) ns)
    rewriteTail _ _ = Nothing

    anyIn :: BindFact -> [Name] -> Bool
    anyIn f ns = any (\n -> Map.member n f) ns

    replace :: BindFact -> Name -> Name
    replace f n = fromMaybe n (Map.lookup n f)

printBindFacts :: FactBase BindFact -> Doc
printBindFacts = printFB printFact
  where
    printFact :: (Label, Map Name Name) -> Doc
    printFact (l, ns) = text (show l) <> text ":" <+> commaSep (text . show) (Map.toList ns)

-- Closure/App collapse (aka "Beta-Fun" from "Compiling with
-- Continuations, Continued" section 2.3)
--
--   v0 <- closure f {x}
--   v1 <- v0 @ y 
--    ==>
--   v1 <- f(x,y)  if f only takes two arguments
-- 
type CollapseFact = Map Name (WithTop TailM)

collapse :: ProgM C C -> ProgM C C
collapse body = runSimpleUniqueMonad $ runWithFuel infiniteFuel collapse'
  where
    entries = entryPoints body
    initial = mapFromList (zip (map fst entries) (repeat Map.empty))
    collapse' :: SimpleFuelMonad (ProgM C C)
    collapse' = do
      (p, _, _) <- analyzeAndRewriteFwd fwd (JustC (map fst entries)) body initial
      return p
    fwd = FwdPass { fp_lattice = collapseLattice
                  , fp_transfer = collapseTransfer
                  , fp_rewrite = collapseRewrite (Map.fromList entries) }

collapseTransfer :: FwdTransfer StmtM CollapseFact
collapseTransfer = mkFTransfer fw
  where
    fw :: StmtM e x -> CollapseFact -> Fact x CollapseFact
    fw (Bind v t@(Closure _ _)) f = Map.insert v (PElem t) f
    fw (CaseM _ _) _ = mkFactBase collapseLattice []
    fw (Done _) _ = mkFactBase collapseLattice []
    fw (BlockEntry _ _ _) f = f
    fw (CloEntry _ _ _ _) f = f

collapseRewrite :: FuelMonad m => Map Label (StmtM C O) -> FwdRewrite m StmtM CollapseFact
collapseRewrite entries = mkFRewrite rewriter
  where
    rewriter :: FuelMonad m => forall e x. StmtM e x -> CollapseFact -> m (Maybe (ProgM e x))
    rewriter (Bind v (Enter f x)) col = 
      case Map.lookup f col of
        Just (PElem (Closure dest@(_, l) vs)) -> 
          case entries ! l of
            (BlockEntry _ _ _) -> bind v (Just (Goto dest (x : vs)))
            (CloEntry _ _ _ _) -> return Nothing
        _ -> return Nothing
    rewriter _ _ = return Nothing

collapseLattice :: DataflowLattice CollapseFact
collapseLattice = DataflowLattice { fact_name = "Closure collapse"
                                  , fact_bot = Map.empty
                                  , fact_join = joinMaps (extendJoinDomain extend) }
  where
    extend :: Label 
           -> OldFact TailM 
           -> NewFact TailM 
           -> (ChangeFlag, WithTop TailM)
    extend _ (OldFact old) (NewFact new) 
      | old == new = (NoChange, PElem new)
      | otherwise = (SomeChange, Top)

--

-- Find CloEntry blocks which do not immediately
-- return a closure and move that code to a block.

-- | Find blocks which have CloEntry labels but
-- do more than capture a closure. Return 
-- findBlocks :: ProgM C C -> FactBase (Maybe Label)
-- findBlocks body = runSimpleUniqueMonad $ runWithFuel infiniteFuel findBlocks' 
--   where
--     findBlocks' :: SimpleFuelMonad (FactBase (Maybe Label))
--     findBlocks' = do
--       (_, f, _) <- analyzeAndRewriteBwd bwd (JustC (map fst (entryPoints body))) body mapEmpty
--       return f
--     bwd = BwdPass { bp_lattice = addBlockLattice
--                   , bp_transfer = addBlockTransfer
--                   , bp_rewrite = noBwdRewrite } 

-- addBlockLattice :: DataflowLattice (Maybe Label)
-- addBlockLattice = DataflowLattice { fact_name = "Find blocks"
--                                   , fact_bot = Nothing
--                                   , fact_join = extend }
--   where
--     extend _ (OldFact old) (NewFact new) = (changeIf (old /= new), new)

-- addBlockTransfer :: BwdTransfer StmtM (Maybe Label)
-- addBlockTransfer = mkBTransfer bw
--   where
--     bw :: StmtM e x -> Fact x (Maybe Label) -> Maybe Label
--     bw (CloEntry _ l clo arg) f = maybe Nothing (const (Just l)) f
--     bw (BlockEntry _ _ _) _ = Nothing
--     bw (Bind _ _) _ = Just (error "don't examine Bind case")
--     bw (CaseM _ _) _ = Just (error "don't examine CaseM case")
--     bw (Done (Closure _ _)) _ = Nothing
--     bw (Done _) _ = Just (error "don't examine Done case")
           
-- -- | Move code from CloEntry labels to new blocks; replace
-- -- CloEntry blocks with a goto.
-- addGotoBlocks :: FactBase (Maybe Label) -> ProgM C C -> ProgM C C
-- addGotoBlocks foundLabels body = runSimpleUniqueMonad $ runWithFuel infiniteFuel addBlocks'
--   where
--     addBlocks' :: SimpleFuelMonad (ProgM C C)
--     addBlocks' = do
--       let entries = map fst (entryPoints body)
--       (p, _, _) <- analyzeAndRewriteFwd fwd (JustC entries) body mapEmpty
--       return p
--     fwd = FwdPass { fp_lattice = labelLattice
--                   , fp_transfer = labelTransfer
--                   , fp_rewrite =  addBlockRewrite (Map.fromList (allBlocks body)) }

--     labelLattice :: DataflowLattice (Set Label)
--     labelLattice = DataflowLattice { fact_name = "Visited Label Lattice"
--                                             , fact_bot = Set.empty
--                                             , fact_join = extend }
--     extend _ (OldFact old) (NewFact new) = (changeIf (not (Set.null (new `Set.difference` old)))
--                                            , new)
               
--     labelTransfer :: FwdTransfer StmtM (Set Label)
--     labelTransfer = mkFTransfer fw
--       where
--         fw :: StmtM e x -> Set Label -> Fact x (Set Label)
--         fw (CloEntry _ l _ _) f = l `Set.insert` f 
--         fw (BlockEntry _ l _) f = l `Set.insert` f
--         fw (Bind _ _) f = f
--         fw (CaseM _ alts) f = mkFactBase labelLattice (zip (concatMap altLabels alts) (repeat f))
--         fw (Done t) f = mkFactBase labelLattice (zip (tailLabel t) (repeat f))

--     altLabels :: Alt TailM -> [Label]
--     altLabels (Alt _ _ t) = tailLabel t

--     tailLabel :: TailM -> [Label]
--     tailLabel (Closure (_, l) _) = [l]
--     tailLabel (Goto (_, l) _ ) = [l]
--     tailLabel _ = []

-- type BlockMap = Map Label (Block StmtM C C)

-- addBlockRewrite :: (UniqueMonad m, FuelMonad m) => BlockMap -> FwdRewrite m StmtM (Set Label)
-- addBlockRewrite orig = mkFRewrite rewriter
--   where
--     rewriter :: (UniqueMonad m, FuelMonad m) => forall e x. StmtM e x -> Maybe Label -> m (Maybe (ProgM e x))
--     rewriter (Done _) (Just l) = gotoBlock orig l
--     rewriter (CaseM _ _) (Just l)  = gotoBlock orig l
--     rewriter (Bind _ _) (Just _) = return (Just emptyGraph)
--     rewriter _ _ = return Nothing

--     gotoBlock :: (UniqueMonad m, FuelMonad m) => BlockMap -> Label -> m (Maybe (ProgM O C))
--     gotoBlock orig label  = 
--       withNewLabel $ \bl -> do 
--         let bn = "block" ++ show bl
--             block = orig ! label
--             (CloEntry _ _ clo arg) :: StmtM C O = snd $ getEntryLabel block
--             newBlock = mkFirst (BlockEntry bn bl (clo++[arg])) <*> blockTail block
--         return $ Just (mkLast (Done (Goto (bn, bl) (clo++[arg]))) |*><*| newBlock)

    
-- Testing & Examples

defs = [isnt
       , nil
       , notNil
       , compose
       , mapNot
       , myMap
       , applyNil
       , funky] ++ kennedy1

main = progM defs

-- | Compile, run live analysis and pretty-print a 
-- lambda-definition to it's monadic form. Also prints
-- the live variables for each label.

progM progs = do
  let tops = map fst progs
      compiled def = (def, compileM tops def)

      opt1 = fst . usingLive addLiveRewriter tops
      opt2 = bindSubst 
      opt3 = fst . usingLive deadRewriter tops 
      opt4 = collapse
      -- opt5 prog = 
      --   let cloBlocks = findBlocks prog
      --   in addGotoBlocks cloBlocks prog

      printLive :: FactBase LiveFact -> Block StmtM C x -> Doc
      printLive live p = 
        let label = fst (getEntryLabel p)
            vars = maybe [] Set.elems (lookupFact label live)
            livePrefix = if null vars
                         then text "[nothing live]"
                         else brackets (commaSep text vars) 
        in livePrefix <+> printBlockM p 

      printWithLive :: (Def, ProgM C C) -> Doc
      printWithLive (def, comp) = 
        let live = findLive tops comp
        in printDef def $+$
           vcat' (maybeGraph empty (printLive live) comp)
      
      compile opts = map (opts . compileM tops)
      printResult defs progs = putStrLn (render (vcat' (map ((text "" $+$) . printWithLive) (zip defs progs))))
                     
  putStrLn "\n ========= BEFORE ============"
  printResult (addFVs tops progs) (compile id progs)
  putStrLn "\n ========= AFTER ============="
  printResult (addFVs tops progs) (compile (opt3 . opt2 . opt1) progs)
           
abs :: Var -> (Expr -> Expr) -> Expr
abs v f = Abs v [] (f (Var v))

nil :: Def 
nil = ("nil", def)
  where
    def = abs "xs" $ \xs -> Case xs [Alt "Nil" [] true
                                       , Alt "Cons" ["a", "b"] false]
mapNot :: Def
mapNot = ("mapNot", def)
  where
    def = App (App (Var "myMap") 
                     (Var "isnt"))
          (mkCons (Constr "A" []) mkNil)

applyNil :: Def
applyNil = ("applyNil", def)
  where
    def = App (Var "nil") (Constr "Nil" [])

isnt :: Def
isnt = ("isnt", def)
  where
    def = abs "f" $ \f -> Case f [Alt "True" [] false
                                 , Alt "False" [] true]

notNil :: Def
notNil = ("notNil", def)
  where
    def = abs "xs" $ \xs -> App (Var "isnt") (App (Var "nil") xs)

compose :: Def
compose = ("compose", def)
  where
    def = abs "f" $ \f -> 
              abs "g" $ \g ->
              abs "x" $ \x -> App f (App g x)

myMap :: Def
myMap = ("myMap", def)
  where
    def = abs "f" $ \f ->
          abs "xs" $ \xs ->
          Case xs [Alt "Nil" [] mkNil
                  , Alt "Cons" ["x", "xs"] (mkCons (App f (Var "x"))
                                                   (App (App (Var "myMap") f)
                                                        (Var "xs")))]

funky :: Def
funky  = ("funky", def)
  where
    -- \x y -> (case y of True -> (\z -> z))  x
    def = abs "x" $ \x ->
          abs "y" $ \y ->
          App (Case y [Alt "True" [] (abs "z" id)]) x

-- Collapsing the closures here
-- a little more difficult because const3
-- takes multiple arguments.
collapse1 = [("collapse1", def)]
  where
    def = App (App (App (const3) 
                        true)
               false)
          false
    const3 = abs "a" $ \a -> abs "x" $ \_ -> abs "y" $ \_ -> a

-- Harder to optimize this definition when
-- const3 defined separately.
collapse2 = [("collapse2", def)
            , ("const3", const3)]
  where
    def = App (App (App (Var "const3") 
                        true)
               false)
          false
    const3 = abs "a" $ \a ->
             abs "x" $ \_ ->
             abs "y" $ \_ -> a

-- Live variables were screwed up with this one. You get the same
-- argument in the closure and the argument position:
--
--   bad = (\x {x}. Pair x x) y
--   [x] L1_absBody0 (x) {x}: Pair x x
--   [x,y] L3_bad (x,y):
--           v2 <- closure L1_absBody0 {x}
--           v2 @ y
--
-- Now fixed.
badClosure = ("bad", def)
  where
    --  (\x {}. Pair (g x) x) y
    def = App (abs "x" $ \x -> Constr "Pair" [x, x])
          (Var "y")

kennedy1 = [("kennedy1", def)
           , myFst
           , ("g", abs "x" $ \x -> x)]
  where
    -- From "Compiling with Continuations, Continued" by Andrew Knnedy
    -- Section 2.3, Problem 1
    --
    --   def = fst ((\x -> (g x, x)) y)
    -- 
    def = App (Var "fst") 
          (App (abs "x" $ \x -> 
                  Constr "Pair" [App (Var "g") 
                                     x, x]) 
           (Var "y"))

myFst = ("fst", fstDef)
  where
    fstDef = abs "p" $ \p -> Case p [Alt "Pair" ["l", "r"] (Var "l")]

mkCons :: Expr -> Expr -> Expr                                        
mkCons x xs = Constr "Cons" [x, xs]

mkNil :: Expr
mkNil = Constr "Nil" []

false :: Expr
false = Constr "False" []

true :: Expr
true = Constr "True" []


