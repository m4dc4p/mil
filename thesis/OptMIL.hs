{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module OptMIL

where

import Control.Monad.State (State, execState, modify, gets)
import Text.PrettyPrint 
import Data.List (sort)
import Data.Maybe (fromMaybe, isJust, catMaybes)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Compiler.Hoopl

import Util
import MIL

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
    

{-
  [("absBody4",T)
  ,("absBody7",CloVal ("absBody4",L5) [])
  ,("blockabsBody4",T)
  ,("const3",CloVal ("absBody7",L8) [])
  ,("main",T)]

const3 = \a_ {}. \b_ {}. \c_ {}. c_
[c_] L5_absBody4 (c_) {}: L6_blockabsBody4(c_)
[c_] L6_blockabsBody4 (c_): return c_
[nothing live] L8_absBody7 (b_) {}: closure L5_absBody4 {}
[nothing live] L9_const3 (a_) {}: closure L8_absBody7 {}

main = ((const3 1) 2) 3
[1,2,3] L2_main (1,2,3):
          v0 <- const3 @ 1
          v1 <- v0 @ 2
          v1 @ 3

L2_main (1,2,3):
  v1 <- return 2
  v1 @ 3
L5_absBody4 (c_) {}: L6_blockabsBody4(c_)
L6_blockabsBody4 (c_): return c_
L8_absBody7 (b_) {}: closure L5_absBody4 {}
L9_const3 (a_) {}: closure L8_absBody7 {}

-}
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

