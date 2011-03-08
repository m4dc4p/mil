{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module OptMIL (mostOpt, addLive, LiveFact
              , getEntryLabel, findLive)

where

import Control.Monad.State (State, execState, modify, gets)
import Text.PrettyPrint 
import Data.List (sort, (\\), elemIndex)
import Data.Maybe (fromMaybe, isJust, catMaybes, fromJust)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Compiler.Hoopl

import Util
import MIL

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

nameOfEntry :: StmtM C O -> Name
nameOfEntry = fst . destOfEntry

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
    live (Bind v t) f = woTops (Set.delete v f  `Set.union` tailVars t )
    live (CaseM v alts) f = woTops (Set.insert v (Set.unions (map (setAlt f) alts)))
    live (Done t) f = woTops (tailVars t)

    woTops :: LiveFact -> LiveFact
    woTops live = live `Set.difference` tops
    
    setAlt :: FactBase LiveFact -> Alt TailM -> Set Name
    setAlt f (Alt _ ns e) = Set.difference (tailVars e) (Set.fromList ns)

    -- | Returns variables used in a tail expression.
    tailVars :: TailM -> Set Name
    tailVars (Closure _ vs) = Set.fromList vs 
    tailVars (Goto _ vs) = Set.fromList vs
    tailVars (Enter v1 v2) = Set.fromList [v1, v2]
    tailVars (ConstrM _ vs) = Set.fromList vs
    tailVars (Return n) = Set.singleton n
    tailVars (Thunk _ vs) = Set.fromList vs
    tailVars (Run n) = Set.singleton n
    tailVars (Prim _ vs) = Set.fromList vs
    tailVars (LitM _) = Set.empty
                        
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
    -- A little questionable - primitives may have effects. But all of those
    -- defined so far do not.
    safe (Prim _ _) = True 
    safe (Enter _ _) = True
    safe (Goto _ _) = True -- Only if block called has no side effects
    safe (LitM _) = True
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
type BindFact = Map Name BindVal

-- | Represents the right side of a bind, for possible
-- substitution.
data BindVal = BindReturn Name -- ^ Return a variable with the given name.
             | BindEnter Name Name -- ^ Enter function with argument.
             | BindClosure Dest [Name] -- ^ Create value.
             | BindGoto Dest [Name] -- ^ Goto block.
             | BindConstrM Name [Name] -- ^ Create value.
             | BindThunk Dest [Name] -- ^ Monadic thunk
             | BindRun Name -- ^ Run a monadic computatino
             | BindPrim Name [Name] -- ^ Primitive call with teh given name and arguments.
  deriving (Eq, Show)

-- | Find "useless" bindings and remove them. Useless bindings 
-- include:
--
--   * bindings which return a value (x <- return y)
--   * bindings which are followed by a return.
--
-- This function really does two separate optimizations (eliminating
-- tails & removing useless binds) that should be separate.
bindSubst :: ProgM C C -> ProgM C C
bindSubst body = runSimple $ do
      let entries = entryLabels body
          initial :: FactBase BindFact
          initial = mapFromList (zip entries (repeat Map.empty))
      (p, _, _) <- analyzeAndRewriteFwd fwd (JustC entries) body initial
      return p
  where
    fwd :: FwdPass SimpleFuelMonad StmtM BindFact
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
    fw (Bind v (Return w)) m = Map.insert v (BindReturn w) m 
    fw (Bind v (Enter f x)) m = Map.insert v (BindEnter f x) m 
    fw (Bind v (Closure d ns)) m = Map.insert v (BindClosure d ns) m 
    fw (Bind v (Goto d ns)) m = Map.insert v (BindGoto d ns) m 
    fw (Bind v (ConstrM c ns)) m = Map.insert v (BindConstrM c ns) m 
    fw (Bind v (Thunk d ns)) m = Map.insert v (BindThunk d ns) m 
    fw (Bind v (Run n)) m = Map.insert v (BindRun n) m 
    fw (Bind v (Prim p vs)) m = Map.insert v (BindPrim p vs) m 
    fw (Bind v (LitM _)) m = m 
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
        | maybe False isNameBind (Map.lookup v f) = _case (substName f v) Just alts
        | otherwise = _case v (replaceAlt f) alts
        where
          replaceAlt f (Alt c ns t) 
            | anyNamesIn f ns = Just $ substNames f ns (\ns -> Alt c ns t)
            | otherwise = maybe Nothing (Just . Alt c ns) (rewriteTail f t)
    rewrite (Done t) f = done (rewriteTail f t)
    rewrite _ _ = return Nothing

    rewriteTail :: BindFact -> TailM -> Maybe TailM
    rewriteTail f (Return v) = substReturn f v 
    rewriteTail f (Enter v w) 
      | anyNamesIn f [v,w] = Just $ substNames f [v, w] (\ [v,w] -> Enter v w)
    rewriteTail f (Closure d ns) 
      | anyNamesIn f ns = Just $ substNames f ns (\ns -> Closure d ns)
    rewriteTail f (Goto d ns) 
      | anyNamesIn f ns = Just $ substNames f ns (\ns -> Goto d ns)
    rewriteTail _ _ = Nothing

    substReturn :: BindFact -> Name -> Maybe TailM
    substReturn f v =
      case Map.lookup v f of
        (Just (BindReturn n)) -> Just $ Return n
        (Just (BindEnter fn x)) -> Just $ substNames f [fn, x] (\ [fn, x] -> Enter fn x)
        (Just (BindClosure d ns)) -> Just $ substNames f ns (\ns -> Closure d ns)
        (Just (BindGoto d ns)) -> Just $ substNames f ns (\ns -> Goto d ns)
        (Just (BindConstrM c ns)) -> Just $ substNames f ns (\vs -> ConstrM c ns)
        (Just (BindThunk d ns)) -> Just $ substNames f ns (\ns -> Thunk d ns)
        (Just (BindRun n)) -> Just $ substNames f [n] (\ [n] -> Run n)
        (Just (BindPrim p vs)) -> Just $ substNames f vs (\vs -> Prim p vs)
        _ -> Nothing

    -- | Find the name to substitue for the one
    -- given, if any. Return the original name
    -- if no substitution applies.
    substName :: BindFact -> Name -> Name
    substName f v = case Map.lookup v f of
                      (Just (BindReturn v')) -> v'
                      _ -> v

    -- | Rewrite the names given according to facts, if those
    -- facts rewrite names. Otherwise, return original names. Order
    -- of the names is preserved.
    substNames :: BindFact -> [Name] -> ([Name] -> a) -> a
    substNames f ns mkA = mkA (foldr doSubst [] ns)
      where
        doSubst v names = substName f v : names

    -- | Indicates if any of the names given
    -- have BindReturn substitutions.
    anyNamesIn :: BindFact -> [Name] -> Bool
    anyNamesIn f ns = any (\n -> maybe False isNameBind $ Map.lookup n f) ns

    isNameBind (BindReturn _) = True
    isNameBind _ = False

printBindFacts :: FactBase BindFact -> Doc
printBindFacts = printFB printFact
  where
    printFact :: (Label, Map Name BindVal) -> Doc
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

-- | Associates a label with the destination which it either captures
-- (Closure) or jumps to (Goto). We store the index at which the
-- argument to a closure will be stored, if it is used.
data DestOf = Jump Dest 
            | Capture Dest (Maybe Int)
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
    initial = mapFromList (zip labels (repeat (topFacts body)))
    -- We determine if each top-level name only allocates
    -- a closure or not, and use that as our initial facts.
    topFacts :: ProgM C C -> CollapseFact
    topFacts = Map.fromList . map factForBlock . allBlocks
    -- Conceptually, all top-level labels hold a closure pointing to
    -- the entry point of the procedure. We don't implement it
    -- that way but the below will fake it for purposes of this
    -- optimization. 
    --
    -- TODO: Filter the initial facts to top-level names only, the below
    -- will create an entry for all labels.
    factForBlock :: (Dest, Block StmtM C C) -> (Name, WithTop CloVal)
    factForBlock (dest@(name, _), block) = (name, PElem (CloVal dest [])) 
    destOf :: ProgM C C -> Label -> Maybe (Label, DestOf)
    destOf body l = case blockOfLabel body l of
                   Just (_,  block) ->
                     case blockToNodeList' block of
                       (JustC (CloEntry {}), [], JustC (Done (Goto d _))) -> Just (l, Jump d)
                       (JustC (CloEntry _ _ _ arg), [], JustC (Done (Closure d args))) -> Just (l, Capture d (arg `elemIndex` args))
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
    fw s@(CaseM _ alts) bound = mkFactBase collapseLattice (zip (stmtSuccessors s) (repeat bound))
    fw s@(Done _) bound = mkFactBase collapseLattice  (zip (stmtSuccessors s) (repeat bound))
    fw (BlockEntry _ _ _) f = f
    fw (CloEntry _ _ _ _) f = f
    
collapseRewrite :: FuelMonad m => Map Label DestOf -> FwdRewrite m StmtM CollapseFact
collapseRewrite blocks = iterFwdRw (mkFRewrite rewriter)
  where
    rewriter :: FuelMonad m => forall e x. StmtM e x -> CollapseFact -> m (Maybe (ProgM e x))
    rewriter (Done (Enter f x)) col = done (collapse col f x)
    rewriter (Bind v (Enter f x)) col = bind v (collapse col f x)
    rewriter _ _ = return Nothing

    collapse col f x =       
      case Map.lookup f col of
        Just (PElem (CloVal dest@(_, l) vs)) -> -- Just (Closure dest (vs ++ [x]))
          case l `Map.lookup` blocks of
            Just (Jump dest) -> Just (Goto dest (vs ++ [x]))
            Just (Capture dest (Just idx)) -> Just (Closure dest (insertAt vs idx x))
            Just (Capture dest _) -> Just (Closure dest vs)
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
    rewriter (Bind v (Goto dest vs)) (Just True) = return (inlineBind v dest vs)
    rewriter (Done (Goto dest vs)) _ = 
      case singlePred preds dest Nothing of
        Just True -> return (inlineDone dest vs)
        _ -> return Nothing

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
          changeTail env (LitM i) = LitM i
          changeTail env (Thunk dest vs) = Thunk dest (map (changeVar env) vs)
          changeTail env (Run v) = Run (changeVar env v)
          changeTail env (Prim p vs) = Prim p (map (changeVar env) vs)
          changeVar env f = Map.findWithDefault f f env

-- | Maps labels to their predecessors. The values
-- for a given key represent predecessors for that
-- block.
type BlockPredecessors = Map Dest [Dest]

-- | Names the set of live blocks (i.e., those
-- that can be called from elsewhere) in a program.
type LiveBlock = Set Dest

-- This doesn't find blocks which are passed
-- as arguments: ((f x) plus) 
--
-- It only recognizes blocks that are explicitly targets of 
-- closure or goto statements.
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

-- | deadBlocks tends to eliminate entry points
-- we would need for separate compilation.
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

-- Goto/Return eliminatino
-- When a Goto jumps to a block that immediately calls a primitive, or
-- returns a value, we inline the block:
--
--  L1: return r
--   ...
--  L2: v <- goto l1 (x)
-- ==>
--  L2: v <- return x
--
-- Bind/subst elimination can take care of the return left over.

-- | Blocks we can inline will be stored in the map, by 
-- label/name. 
type ReturnPrimBlocks = Map Dest ReturnType

-- | Used during analysis - indicates if
-- a block can be inlined like we want.
type ReturnPrimBlock = Maybe ReturnType

-- | Doesn't carry any useful information,
-- used by our rewriter since it calculates no
-- new facts.
type EmptyFact = ()

-- | Used to indicate what kind of instruction can be inlined
-- from a block. 
data ReturnType = TmpRet Name 
    | TmpPrim Name [Name] 
    | AReturn Name Int 
    | APrim Name [Name] [Int]
  deriving (Eq, Show)

-- | Inline blocks that call primitives or
-- only return a value.
inlineReturn :: ProgM C C -> ProgM C C
inlineReturn body = 
    runSimple $ do
      fresh <- freshLabel

      -- First we find all the blocks which we
      -- could inline
      (_, f, _) <- analyzeAndRewriteBwd bwdAnalysis (JustC labels) body (initial bwdAnalysis)
    
      -- Turn our facts into a proper map of Dest -> Fact, then
      -- use those facts to rewrite and inline.
      let returnBlocks = Map.fromList . map toDest . filter (isJust . snd) .  mapToList $ f
          toDest (l, Just f) = (fromJust (labelToDest body l), f)
      (body', _, _) <- analyzeAndRewriteBwd (bwdRewrite returnBlocks) (JustC labels) body (initial (bwdRewrite returnBlocks))
      return body'
  where              
    labels = entryLabels body
    initial bwd = mkFactBase (bp_lattice bwd) (zip labels (repeat (fact_bot (bp_lattice bwd))))
    bwdRewrite :: ReturnPrimBlocks -> BwdPass SimpleFuelMonad StmtM EmptyFact
    bwdRewrite returnBlocks = BwdPass { bp_lattice = rewriteLattice
                                      , bp_transfer = mkBTransfer noOpTrans
                                      , bp_rewrite = inlineReturnRewrite returnBlocks }
    rewriteLattice :: DataflowLattice EmptyFact
    rewriteLattice = DataflowLattice { fact_name = "Goto/Return"
                                     , fact_bot = ()
                                     , fact_join = extend }
    bwdAnalysis :: BwdPass SimpleFuelMonad StmtM ReturnPrimBlock
    bwdAnalysis = BwdPass { bp_lattice = analysisLattice
                          , bp_transfer = inlineReturnTransfer 
                          , bp_rewrite = noBwdRewrite }
    analysisLattice = DataflowLattice { fact_name = "Goto/Return"
                                      , fact_bot = Nothing
                                      , fact_join = extend }
    extend _ (OldFact old) (NewFact new) = (changeIf (old /= new), new)
    -- A no-op transfer function. Used during rewrite since we 
    -- don't gather any new facts.
    noOpTrans :: StmtM e x -> Fact x EmptyFact -> EmptyFact
    noOpTrans _ _ = ()

inlineReturnTransfer :: BwdTransfer StmtM ReturnPrimBlock
inlineReturnTransfer = mkBTransfer bw
  where
    bw :: StmtM e x -> Fact x ReturnPrimBlock -> ReturnPrimBlock
    bw (Done (Return v)) f = Just (AReturn v (-1))
    bw (Done (Prim p vs)) f = Just (APrim p vs [])
    bw (BlockEntry name lab args) (Just (AReturn v _)) =
      case v `elemIndex` args of
        Just idx -> Just (AReturn v idx)
        _ -> Nothing
    bw (BlockEntry name lab args) (Just (APrim p vs _)) =
      Just (APrim p vs (catMaybes $ map (`elemIndex` args) vs))
    bw _ _ = Nothing

inlineReturnRewrite :: FuelMonad m => ReturnPrimBlocks -> BwdRewrite m StmtM EmptyFact
inlineReturnRewrite blocks = iterBwdRw (mkBRewrite rewriter)
  where
    rewriter :: FuelMonad m => forall e x. StmtM e x -> Fact x EmptyFact -> m (Maybe (ProgM e x))
    rewriter (Bind v (Goto dest vs)) _ =
      case dest `Map.lookup` blocks of
        Just at -> return (Just (mkMiddle (Bind v (newTail at vs))))
        _ -> return Nothing
    rewriter (Done (Goto dest@(_, l) vs)) _ =
      case dest `Map.lookup` blocks of
        Just at -> return (Just (mkLast (Done (newTail at vs))))
        _ -> return Nothing
    rewriter _ _ = return Nothing

    newTail (AReturn _ i) vs = Return (vs !! i)
    newTail (APrim p _ idxs) vs = Prim p (map (vs !!) idxs)

-- Useful combinations of optimizations

addLive tops = fst . usingLive addLiveRewriter tops
    
-- | Eliminate dead code in blocks.  
deadCode :: [Name] -> ProgM C C -> ProgM C C
deadCode tops = fst . usingLive deadRewriter tops

-- | Collapse closures, then elminate dead assignments
-- in blocks.
optCollapse tops = fst . usingLive deadRewriter tops . collapse

-- | Inline blocks which only return or call a primitive, then
-- eliminate dead code within blocks.
inlineSimple tops = deadCode tops . bindSubst . inlineReturn 

mostOpt :: [Name] -> ([Name], ProgM C C) -> ProgM C C -> ProgM C C
mostOpt userTops prelude@(prims, _) body = 
    newTops deadBlocks . 
    inlineBlocks tops . 
    newTops deadBlocks .  
    inlineSimple tops . 
    newTops optCollapse . 
    deadCode tops . 
    bindSubst .
    addLive tops $ body
  where
    newTops :: ([Name] -> ProgM C C -> ProgM C C) -> ProgM C C -> ProgM C C
    newTops f b = f (userTops ++ primTops b) b
    tops = userTops ++ primTops body
    primTops :: ProgM C C -> [Name]
    primTops body = 
      let allLive = Set.unions . mapElems $ findLive [] body
      in filter (`Set.member` allLive) prims
