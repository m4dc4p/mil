{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module OptMIL (mostOpt, addLive, LiveFact
              , getEntryLabel, findLive, deadCode)

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
import Live
import DeadBlocks
import TrimTailX

-- From mon5.lhs
--   v <- return w; c  
--        ==>  c       if v == w
--        ==> [w/v] c  otherwise 
--
-- in Hoopl/MIL terms:
--
--   Bind v (Return w) <*> c  
--        ==> c    if v==w
--        ==> [w/v] c  otherwise
--

-- | Associates a binding (the key) with the
-- value that should be substituted for it. 
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
             | BindPrim Name [Name] -- ^ Primitive call with the given name and arguments.
  deriving (Eq, Show)

-- | Find "useless" bindings and remove them. Useless bindings 
-- include:
--
--   * bindings which return a value (x <- return y; c ==> [x/y] c)
--   * bindings which are followed by a return. (x <- y; return x ==> y)
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
    fw (Bind v (LitM _)) m = Map.delete v m
    fw (BlockEntry _ _ _) m = m
    fw (CloEntry _ _ _ _) m = m
    fw (CaseM _ alts) m = 
      mkFactBase bindSubstLattice []
    fw (Done _ _ t) m = 
      mkFactBase bindSubstLattice []

bindSubstRewrite :: FuelMonad m => FwdRewrite m StmtM BindFact
bindSubstRewrite = 
    -- deep rewriting used
    -- so all possible
    -- substitutions occur
    iterFwdRw (mkFRewrite rewrite) 
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
    rewrite (Done n l t) f = done n l (rewriteTail f t)
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
        -- (Just (BindRun n)) -> Just $ substNames f [n] (\ [n] -> Run n)
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
                       (JustC (CloEntry {}), [], JustC (Done _ _ (Goto d _))) -> Just (l, Jump d)
                       (JustC (CloEntry _ _ _ arg), [], JustC (Done _ _ (Closure d args))) -> Just (l, Capture d (arg `elemIndex` args))
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
    fw s@(Done _ _ _) bound = mkFactBase collapseLattice  (zip (stmtSuccessors s) (repeat bound))
    fw (BlockEntry _ _ _) f = f
    fw (CloEntry _ _ _ _) f = f
    
collapseRewrite :: FuelMonad m => Map Label DestOf -> FwdRewrite m StmtM CollapseFact
collapseRewrite blocks = iterFwdRw (mkFRewrite rewriter)
  where
    rewriter :: FuelMonad m => forall e x. StmtM e x -> CollapseFact -> m (Maybe (ProgM e x))
    rewriter (Done n l (Enter f x)) col = done n l (collapse col f x)
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
                  , bp_transfer = inlineTransfer preds 
                  , bp_rewrite = inlineRewrite preds body }


inlineLattice :: DataflowLattice InlineFact
inlineLattice = DataflowLattice { fact_name = "Inline blocks"
                                , fact_bot = Nothing
                                , fact_join = extend }
  where
    extend _ (OldFact old) (NewFact new) = (changeIf (old /= new)
                                           , new)

inlineTransfer :: BlockPredecessors -> BwdTransfer StmtM InlineFact
inlineTransfer preds = mkBTransfer bw
  where
    -- Find blocks which are the sole predecessor to another
    -- block. 
    bw :: StmtM e x -> Fact x InlineFact -> InlineFact
    bw (Bind v (Goto dest vs)) f = singlePred preds dest f 
    bw (Bind {}) f = f
    bw (CaseM {}) _ = Just False
    bw (Done _ _ (Goto dest _)) f = Nothing -- singlePred preds dest Nothing
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
    rewriter (Done _ _ (Goto dest vs)) _ = 
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
          rename (Done _ _ tail) (env, prog) = (env, prog <*> mkMiddle (Bind result (changeTail env tail)))
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

-- Goto/Return elimination
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

inlineReturnTransfer :: BwdTransfer StmtM ReturnPrimBlock
inlineReturnTransfer = mkBTransfer bw
  where
    bw :: StmtM e x -> Fact x ReturnPrimBlock -> ReturnPrimBlock
    bw (Done _ _ (Return v)) f = Just (AReturn v (-1))
    bw (Done _ _ (Prim p vs)) f = Just (APrim p vs [])
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
    rewriter (Done n label (Goto dest@(_, l) vs)) _ =
      case dest `Map.lookup` blocks of
        Just at -> return (Just (mkLast (Done n label (newTail at vs))))
        _ -> return Nothing
    rewriter _ _ = return Nothing

    newTail (AReturn _ i) vs = Return (vs !! i)
    newTail (APrim p _ idxs) vs = Prim p (map (vs !!) idxs)

-- | Collapse closures, then elminate dead assignments
-- in blocks.
optCollapse tops = deadCode . collapse

-- | Inline blocks which only return or call a primitive, then
-- eliminate dead code within blocks.
inlineSimple tops = deadCode . bindSubst . inlineReturn 

mostOpt :: [Name] -> ([Name], ProgM C C) -> ProgM C C -> ProgM C C
mostOpt userTops prelude@(prims, _) body = addLive tops .
    trimTail .
    newTops deadBlocks . 
    inlineBlocks tops . 
    newTops deadBlocks .  
    inlineSimple tops . 
    newTops optCollapse . 
    deadCode . 
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
