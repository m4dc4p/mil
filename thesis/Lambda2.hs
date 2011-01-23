{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module Lambda2

where

import Prelude hiding (abs)
import Control.Monad.State (State, execState, modify, gets)
import Text.PrettyPrint 
import Data.List (intersperse, (\\), union, nub, delete, sort)
import Data.Maybe (fromMaybe, isJust, catMaybes)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Compiler.Hoopl

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

type ProgM = Graph StmtM

-- Compiling from lambda-calculus to the monadic language.

compileM :: [Name] -> Int -> Def -> (Int, ProgM C C)
compileM tops labelSeed def = 
  let result = foldr compDef initial $ prepareExpr tops [def]
  in (compI result + 1, compG result)
  where
    compDef p = execState (uncurry newDefn p)
    initial = C labelSeed emptyClosedGraph tops
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
               
type CompM = State CompS

-- | Add a name to the list of top-level functions.
addName :: Name -> CompM ()
addName name = modify (\s@(C { compT }) -> s { compT = name : compT })

-- | Make a new top-level function name, based on the
-- prefix given.
newTop :: Name -> CompM Name
newTop name = do
  f <- fresh name
  addName f
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
stmtSuccessors (CaseM _ alts) = map snd (concatMap (\(Alt _ _ t) -> tailDest t) alts)
stmtSuccessors (Done t) = map snd (tailDest t)

tailDest :: TailM -> [Dest]
tailDest (Closure dest _) = [dest]
tailDest (Goto dest _) = [dest]
tailDest _ = []

-- | Annotate lambda-calculus programs with free variables and
-- rename variables so we can always generate safe fresh names.
prepareExpr :: [Name] -> Prog -> Prog
prepareExpr tops = addFVs . renameVars 
  where
    addFVs = map (\(name, body) -> (name, snd $ annotate body))
    -- All variables have an underscore attached. The compiler will
    -- never generate variables with underscores, guaranteeing
    -- it can always create a fresh variable name.
    renameVars = map (\(name, body) -> (name, renameInExpr Map.empty body))
    renameInExpr :: Map Name Name -> Expr -> Expr
    renameInExpr env (Abs vs [] b) = 
      let ([vs'], env') = addNames env [vs]
      in Abs vs' [] (renameInExpr env' b)
    renameInExpr env (App e1 e2) = App (renameInExpr env e1) (renameInExpr env e2)
    renameInExpr env (Case e alts) = 
      let alts' = map (renameAlt env) alts
      in Case (renameInExpr env e) alts'
    renameInExpr env (Constr c exprs) = 
      Constr c (map (renameInExpr env) exprs)
    renameInExpr env (Var v) 
                 | v `Map.member` env  = Var (env ! v)
                 | otherwise = Var v
    renameAlt env (Alt c ns e) = 
      let (ns', env') = addNames env ns
      in Alt c ns' (renameInExpr env' e)
    addNames env vs = 
      let vs' = map (++ "_") vs
      in  (vs', env `Map.union` Map.fromList (zip vs vs'))
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
printProgM = vcat' . maybeGraphCC empty printBlockM

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

maybeGraphCC :: b -> (block node C C -> b) -> Graph' block node C C -> [b]
maybeGraphCC b f (GMany _ middles _) = map f . mapElems $ middles

-- | Get all the labels at entry points in 
-- the program.
entryPoints :: ProgM C C -> [(Label, StmtM C O)]
entryPoints (GMany _ blocks _) = map getEntryLabel (mapElems blocks)

allBlocks :: ProgM C C -> [(Dest, Block StmtM C C)]
allBlocks (GMany _ blocks _) = map blockToDest (mapElems blocks)

blockToDest :: Block StmtM C C -> (Dest, Block StmtM C C)
blockToDest block = (destOfEntry (blockEntry block), block)

-- | Get the first instruction in a block.
blockEntry :: Block StmtM C C -> StmtM C O
blockEntry b = case blockToNodeList' b of
                 (JustC entry, _, _) -> entry


-- | Get the tail of a block. Will exclude
-- the entry instruction (if C C) or the
-- first instruction in the block (O C)
blockTail :: Block StmtM x C -> ProgM O C
blockTail b = case blockToNodeList' b of
                (_, mid, JustC end) -> mkMiddles mid <*> mkLast end

-- | Find a block with a given label in the propgram
-- and return it paired with it's label and name.
blockOfLabel :: ProgM C C -> Label -> Maybe (Dest, Block StmtM C C)
blockOfLabel body l = case lookupBlock body l of
                  BodyBlock block -> Just (blockToDest block)
                  _ -> Nothing

getEntryLabel :: Block StmtM C x -> (Label, StmtM C O)
getEntryLabel block = case blockToNodeList' block of
  (JustC e@(BlockEntry _ l _), _, _) -> (l, e)
  (JustC e@(CloEntry _ l _ _), _, _) -> (l, e)

entryLabels :: ProgM C C -> [Label]
entryLabels = map fst . entryPoints 

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

-- | Run a Hoopl optimization pas with infinite fuel,
-- using the monad Hoopl provides.
runSimple :: SimpleFuelMonad a -> a
runSimple p = runSimpleUniqueMonad $ runWithFuel infiniteFuel p
    
nameOfEntry :: StmtM C O -> Name
nameOfEntry = fst . destOfEntry

destOfEntry :: StmtM C O -> Dest
destOfEntry (BlockEntry n l _) = (n, l)
destOfEntry (CloEntry n l _ _) = (n, l)

-- Determining liveness in StmtM

type LiveFact = Set Name

-- | Used to apply different rewriters which all require 
-- live variable analysis.
usingLive :: (forall m. FuelMonad m => BwdRewrite m StmtM LiveFact) -- ^ Rewrite to use
          -> [Name] -- ^ Top-level variables
          -> ProgM C C -- ^ Program to rewrite
          -> (ProgM C C, FactBase LiveFact) -- Results
usingLive rewriter tops body = runSimple $ do
      (p, f, _) <- analyzeAndRewriteBwd bwd (JustC (entryLabels body)) body mapEmpty
      return (p, f)
  where
    bwd = BwdPass { bp_lattice = liveLattice "live statements" :: DataflowLattice LiveFact
                  , bp_transfer = liveTransfer (Set.fromList tops)
                  , bp_rewrite = rewriter } 

-- | Initial setup for liveness analysis.
liveLattice :: Ord a => String -> DataflowLattice (Set a)
liveLattice name = DataflowLattice { fact_name = name
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
-- deadRewriter implemented similary, where "safe" determines if the
-- expression on the right of the array can be elminiated safely.
-- 
deadRewriter :: FuelMonad m => BwdRewrite m StmtM LiveFact
deadRewriter = mkBRewrite rewrite
  where
    rewrite :: FuelMonad m => forall e x. StmtM e x -> Fact x LiveFact -> m (Maybe (ProgM e x))
    rewrite (Bind v t) f 
            | safe t && not (v `Set.member` f) = return (Just emptyGraph)
    rewrite _ _ = return Nothing

    -- Indicates when it is OK to eliminate a tail instruction in a monadic
    -- expression.
    safe :: TailM -> Bool
    safe (Return _) = True
    safe (Closure _ _) = True
    safe (ConstrM _ _) = True
    safe _ = False

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
--

-- | Associates a binding (the key) with the
-- value that should be substituted for it. Only
-- variables that are bound with the form v <- return w
-- end up here.
type BindFact = Map Name Name

-- | Find "useless" bindings which have no visible
-- effect other than allocation and remove them.
bindSubst :: ProgM C C -> ProgM C C
bindSubst body = runSimple $ do
      let entries = entryLabels body
          initial = mapFromList (zip entries (repeat Map.empty))
      (p, _, _) <- analyzeAndRewriteFwd fwd (JustC entries) body initial
      return p
  where
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
--   f1 (t) {x, y,z} : g(x,y,z,t)
--   ...
--   h1:
--     v0 <- closure f1 {x,y,z}
--     v1 <- v0 @ w 
--    ==>
--   h1:
--     v1 <- g(x,y,z,w)  
-- 

-- | Associates a label with the destination
-- which it either captures (Closure) or 
-- jumps to (Goto).
data DestOf = Jump Dest 
            | Capture Dest Bool
              deriving (Eq, Show)

-- | Stores destination and arguments for a 
-- closure value. Mostly to remove annoying
-- GADT type variables.
data CloVal = CloVal Dest [Name]
            deriving (Eq, Show)

-- | Indicates if the given name holds an allocated
-- closure or an unknown value.
type CollapseFact = Map Name (WithTop CloVal) -- Need to track
                                             -- variables stored in a
                                             -- closure as well

-- | Collapse closure allocations - when we can tell a variable holds
-- a closure, and that closure only allocates another closure or jumps
-- to a block, then avoid that extra step and directly allocate the
-- closure or jump to the block.
collapse :: ProgM C C -> ProgM C C
collapse body = runSimple $ do
      (p, _, _) <- analyzeAndRewriteFwd fwd (JustC labels) body initial
      return p
  where
    labels = entryLabels body
    destinations = Map.fromList . catMaybes . map (destOf body) 
    initial = mapFromList (zip labels (repeat Map.empty))
    destOf :: ProgM C C -> Label -> Maybe (Label, DestOf)
    destOf body l = case blockOfLabel body l of
                   Just (_,  block) ->
                     case blockToNodeList' block of
                       (JustC (CloEntry {}), [], JustC (Done (Goto d _))) -> Just (l, Jump d)
                       (JustC (CloEntry _ _ _ arg), [], JustC (Done (Closure d args))) -> Just (l, Capture d (arg `elem` args))
                       _ -> Nothing
                   _ -> Nothing
    fwd = FwdPass { fp_lattice = collapseLattice
                  , fp_transfer = collapseTransfer
                  , fp_rewrite = collapseRewrite (destinations labels) }

collapseTransfer :: FwdTransfer StmtM CollapseFact
collapseTransfer = mkFTransfer fw
  where
    fw :: StmtM e x -> CollapseFact -> Fact x CollapseFact
    fw (Bind v (Closure dest args)) bound = Map.insert v (PElem (CloVal dest args)) bound
    fw (Bind v _) bound = Map.insert v Top bound
    fw (CaseM _ _) _ = mkFactBase collapseLattice []
    fw (Done _) _ = mkFactBase collapseLattice []
    fw (BlockEntry _ _ _) f = f
    fw (CloEntry _ _ _ _) f = f
    
    addUsed binding used arg = Map.insert arg binding used

collapseRewrite :: FuelMonad m => Map Label DestOf -> FwdRewrite m StmtM CollapseFact
collapseRewrite blocks = iterFwdRw (mkFRewrite rewriter)
  where
    rewriter :: FuelMonad m => forall e x. StmtM e x -> CollapseFact -> m (Maybe (ProgM e x))
    rewriter (Done (Enter f x)) col = done (collapse col f x)
    rewriter (Bind v (Enter f x)) col = bind v (collapse col f x)
    rewriter _ _ = return Nothing

    collapse col f x =       
      case Map.lookup f col of
        Just (PElem (CloVal dest@(_, l) vs)) ->
          case l `Map.lookup` blocks of
            Just (Jump dest) -> Just (Goto dest (vs ++ [x]))
            Just (Capture dest usesArg) 
              | usesArg -> Just (Closure dest (vs ++ [x]))
              | otherwise -> Just (Closure dest vs)
            _ -> Nothing
        _ -> Nothing

collapseLattice :: DataflowLattice CollapseFact
collapseLattice = DataflowLattice { fact_name = "Closure collapse"
                                  , fact_bot = Map.empty
                                  , fact_join = joinMaps (extendJoinDomain extend) }
  where
    extend :: Label 
           -> OldFact CloVal
           -> NewFact CloVal
           -> (ChangeFlag, WithTop CloVal)
    extend _ (OldFact old) (NewFact new) 
      | old == new = (NoChange, PElem new)
      | otherwise = (SomeChange, Top)

-- Implementing CC-Let (figure 6) from Kennedy's paper:
--
--   x2 <- (x1 <- A; B); C
-- ==>
--   x1 <- A; x2 <- B; C
--
-- This manifests as inlining in our language:
--
--   L2: x1 <- L1() -- L1 defines A, not shown.
--       ...
--       bN  -- L2 defines B.
--   L3: x2 <- L2()  
--       ...
--       cN   -- L3 defines C.
--
-- which we want to rewrite as:
-- 
--   L3: x1 <- L1()
--       ...
--       x2 <- bN -- If L2 consists only of x1 <- L1() then this statement
--                -- collapses to x2 <- L1() and x1 <- L1() disappears.
--       c1 
--       ...
--       cN
--
-- This program only inlines L2 when only one predecessor exists (i.e.,
-- it has only one caller).

-- Nothing -- unknown
-- Maybe True - will inline
-- Maybe False - will not inline
type InlineFact = Maybe Bool

inlineBlocks :: [Name] -> ProgM C C -> ProgM C C
inlineBlocks tops body = 
  case runInline tops body of
    (True, body') -> inlineBlocks tops (deadBlocks tops body')
    (_, body') -> body'
  where
    runInline tops body = runSimple $ do
      (body', f, _) <- analyzeAndRewriteBwd bwd (JustC labels) body initial
      return (or (catMaybes (mapElems f)), body')
    preds = findBlockPreds tops body
    labels = entryLabels body
    initial = mkFactBase (bp_lattice bwd) (zip labels (repeat Nothing))
    bwd = BwdPass { bp_lattice = inlineLattice
                  , bp_transfer = inlineTransfer preds body
                  , bp_rewrite = inlineRewrite preds body }


inlineLattice :: DataflowLattice InlineFact
inlineLattice = DataflowLattice { fact_name = "Inline blocks"
                                , fact_bot = Nothing
                                , fact_join = extend }
  where
    extend _ (OldFact old) (NewFact new) = (changeIf (old /= new)
                                           , new)

inlineTransfer :: BlockPredecessors -> ProgM C C -> BwdTransfer StmtM InlineFact
inlineTransfer preds prog = mkBTransfer bw
  where
    -- Find blocks which are the sole predecessor to another
    -- block. 
    bw :: StmtM e x -> Fact x InlineFact -> InlineFact
    bw (Bind v (Goto dest vs)) f = singlePred preds dest f 
    bw (Bind {}) f = f
    bw (CaseM {}) _ = Just False
    bw (Done (Goto dest _)) f = Nothing -- singlePred preds dest Nothing -- not yet implemented
    bw (Done {}) _ = Nothing
    bw (CloEntry {}) f = f
    bw (BlockEntry {}) f = f

singlePred :: BlockPredecessors -> Dest -> InlineFact -> InlineFact
singlePred preds dest f 
  | dest `Map.member` preds && null (drop 1 (preds ! dest)) = Just (maybe True (True &&) f)
  | otherwise = f

inlineRewrite :: FuelMonad m => BlockPredecessors -> ProgM C C -> BwdRewrite m StmtM InlineFact
inlineRewrite preds prog = mkBRewrite rewriter
  where
    rewriter :: FuelMonad m => forall e x. StmtM e x -> Fact x InlineFact -> m (Maybe (ProgM e x))
    rewriter (Bind v (Goto dest vs)) (Just False) = return Nothing
    rewriter (Done (Goto dest vs)) _ = 
      case singlePred preds dest Nothing of
        Just True -> return (inlineDone dest vs)
        _ -> return Nothing
    rewriter (Bind v (Goto dest vs)) _ = return (inlineBind v dest vs)

    rewriter _ _ = return Nothing

    inlineDone :: Dest -> [Name] -> Maybe (ProgM O C)
    inlineDone (_, l) args = Nothing -- not yet implemented

    inlineBind :: Name -> Dest -> [Name] -> Maybe (ProgM O O)
    inlineBind result (_, l) args = maybe Nothing (Just . snd . renameInBody . snd) (blockOfLabel prog l)
      where
          renameInBody body = foldGraphNodes rename  
                                             (blockTail body) 
                                             (mkEnv body, emptyGraph)
          -- Create a map from formal arguements
          -- to actual arguments so we can rename.
          mkEnv :: Block StmtM C C -> Map Name Name
          mkEnv body = Map.fromList (zip (entryArgs body) args)
          entryArgs :: Block StmtM C C -> [Name]
          entryArgs body = case blockEntry body of
                             BlockEntry  _ _ args -> args
                             CloEntry _ _ clo arg -> clo ++ [arg]
          rename :: forall e x. StmtM e x -> (Map Name Name, ProgM O O) -> (Map Name Name, ProgM O O)
          rename (Bind v tail) (env, prog) 
            | v `Map.member` env = (Map.delete v env, newProg)
            | otherwise = (env, newProg)
            where
              newProg = prog <*> mkMiddle (Bind v (changeTail env tail))
          rename (Done tail) (env, prog) = (env, prog <*> mkMiddle (Bind result (changeTail env tail)))
          changeTail :: Map Name Name -> TailM -> TailM
          changeTail env (Return n) = Return (changeVar env n)
          changeTail env (Enter f x) = Enter (changeVar env f) (changeVar env x)
          changeTail env (Closure dest vs) = Closure dest (map (changeVar env) vs)
          changeTail env (Goto dest vs) = Goto dest (map (changeVar env) vs)
          changeTail env (ConstrM c ns) = ConstrM c (map (changeVar env) ns)
          changeVar env f = Map.findWithDefault f f env

-- | Maps labels to their predecessors. The values
-- for a given key represent predecessors for that
-- block.
type BlockPredecessors = Map Dest [Dest]

-- | Names the set of live blocks (i.e., those
-- that can be called from elsewhere) in a program.
type LiveBlock = Set Dest

findBlockPreds :: [Name] -> ProgM C C -> BlockPredecessors
findBlockPreds tops body = runSimple $ do
    (_, f, _) <- analyzeAndRewriteBwd bwd (JustC labels) body initial
    return $ Map.fromList (catMaybes (map convert (mapToList f)))
  where
    convert (label, set) = case blockOfLabel body label of
                                 Just (dest, _) -> Just (dest, Set.toList set)
                                 _ -> Nothing
    labels = entryLabels body
    initial = mkFactBase (bp_lattice bwd) (zip labels (repeat (Set.fromList (topLabels body))))
    bwd = BwdPass { bp_lattice = liveLattice "Live blocks" :: DataflowLattice LiveBlock
                  , bp_transfer = liveBlockTransfer
                  , bp_rewrite = noBwdRewrite }
    topLabels :: ProgM C C -> [Dest]
    topLabels = filter (\(n, l) -> n `elem` tops) . map fst . allBlocks
    
liveBlockTransfer :: BwdTransfer StmtM LiveBlock
liveBlockTransfer = mkBTransfer live
  where
    live :: StmtM e x -> Fact x LiveBlock -> LiveBlock
    live (Bind v tail) liveBlocks = Set.fromList (tailDest tail) `Set.union` liveBlocks

    live (CaseM _ alts) liveBlocks = Set.unions (map (Set.fromList . tailDest . altExpr) alts ++ mapElems liveBlocks)
    live (Done tail) liveBlocks =  Set.unions (Set.fromList (tailDest tail) : mapElems liveBlocks)

    live (BlockEntry _ l _) liveBlocks = liveBlocks
    live (CloEntry _ l _ _) liveBlocks = liveBlocks

    altExpr (Alt _ _ e) = e

-- An (failed) experiment attempting to eliminate dead blocks through
-- rewriting. Seems too painful to get Hoopl to work over ``Graph
-- ProgM'' (i.e. graphs of graphs) nodes.
--
-- deadBlockRewrite :: FuelMonad m => BwdRewrite m ProgM LiveBlock
-- deadBlockRewrite = mkBRewrite deadBlocks
--   where
--     deadBlocks :: FuelMonad m => forall e x. ProgM e x -> Fact x LiveBlock -> m (Maybe (Graph ProgM e x))
--     deadBlocks (GMany NothingO blocks _) blockSet = 
--       let theseBlocks :: LabelMap (Block StmtM C C) -> [(Dest, Block StmtM C C)] 
--           theseBlocks = map (blockToDest) . mapElems
--           addBlock :: Dest -> Block ProgM C C -> Graph ProgM C C -> Graph ProgM C C
--           addBlock (_, label) b prog = (GMany NothingO (mapSingleton label b) NothingO) |*><*| prog
--           liveBlocks :: [(Dest, Block StmtM C C)] -> Graph ProgM C C
--           liveBlocks = foldr (\(d,b) -> addBlock d (blockGraph b)) emptyClosedGraph 
--       in undefined

-- instance NonLocal ProgM where
--   entryLabel = undefined
--   successors = undefined

deadBlocks :: [Name] -> ProgM C C -> ProgM C C
deadBlocks tops prog = 
  case removeOrphans (liveSet prog) prog of
    (SomeChange, prog') -> deadBlocks tops prog'
    _ -> prog
  where
    liveSet = Set.fromList . concat . Map.elems . findBlockPreds tops

    removeOrphans :: LiveBlock 
                  -> ProgM C C 
                  -> (ChangeFlag, ProgM C C)
    removeOrphans live = foldl (remove live) (NoChange, emptyClosedGraph) . allBlocks

    remove :: LiveBlock 
                 -> (ChangeFlag, ProgM C C) 
                 -> (Dest, Block StmtM C C) 
                 -> (ChangeFlag, ProgM C C)
    remove live (flag, prog) (dest, block) 
      | dest `Set.member` live = (flag, blockGraph block |*><*| prog)
      | otherwise = (SomeChange, prog)

-- Testing & Examples

defs = [isnt
       , nil
       , notNil
       , compose
       , mapNot
       , myMap
       , applyNil
       , funky] ++ kennedy1 ++
       origExample ++
       origExample2
       

main = progM defs

-- | Compile, run live analysis and pretty-print a 
-- lambda-definition to it's monadic form. Also prints
-- the live variables for each label.

progM progs = do
  let tops = map fst progs

      opt1 = fst . usingLive addLiveRewriter tops
      opt2 = bindSubst 
      opt3 = fst . usingLive deadRewriter tops 
      opt4 = fst . usingLive deadRewriter tops . collapse
      opt5 = deadBlocks tops
      opt6 = deadBlocks tops . inlineBlocks tops

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
           vcat' (maybeGraphCC empty (printLive live) comp)
      
      compileOne opts p (i, ps) = 
        let (j, p') = compileM tops i p
        in (j, (opts p') : ps)

      compile opts = snd . foldr (compileOne opts) (0, []) 

      printResult defs progs = putStrLn (render (vcat' (map ((text "" $+$) . printWithLive) (zip defs progs))))
                     
  putStrLn "\n ========= BEFORE ============"
  printResult (prepareExpr tops progs) (compile opt1 progs)
  putStrLn "\n ========= AFTER ============="
  printResult (prepareExpr tops progs) (compile (opt6 . opt5 . opt4 . opt3 . opt2 . opt1) progs)
           
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
compose = ("compose", composeDef)
composeDef = abs "f" $ \f -> 
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

origExample = [("main", App (App composeDef 
                            (Var "foo")) (Var "bar"))
              , compose]

origExample2 = [("main", App (App (App composeDef 
                                   (Var "foo")) 
                              (Var "bar"))
                 (Var "baz"))
              , compose]

const3 = [("const3", const3Def)
         , ("main", App (App (App const3Def 
                                  (Var "1")) 
                              (Var "2")) 
                        (Var "3"))]
  where
    const3Def = abs "a" $ \_ ->
                abs "b" $ \_ ->
                abs "c" $ \c -> c
mkCons :: Expr -> Expr -> Expr                                        
mkCons x xs = Constr "Cons" [x, xs]

mkNil :: Expr
mkNil = Constr "Nil" []

false :: Expr
false = Constr "False" []

true :: Expr
true = Constr "True" []


