%if False

> {-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
>   , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}
> module DeadBlocks (deadBlocks, BlockPredecessors, findBlockPreds)
>
> where 
>
> import Control.Monad.State (State, execState, modify, gets)
> import Text.PrettyPrint 
> import Data.List (sort, (\\), elemIndex)
> import Data.Maybe (fromMaybe, isJust, catMaybes, fromJust)
> import Data.Map (Map, (!))
> import qualified Data.Map as Map
> import Data.Set (Set)
> import qualified Data.Set as Set
> 
> import Compiler.Hoopl
> 
> import Util
> import MIL
> import Live
>

%endif

Our first analysis finds all the blocks referenced within a 
given block, which we call the |LiveBlock| set.

> type LiveBlock = Set Dest

To find the live blocks, we proceed backward over each
block, collecting all the blocks called. This portion of
the analysis does not do any rewriting, so there is no
rewrite function to show.
\savecolumns

> liveBlockTransfer :: BwdTransfer StmtM LiveBlock
> liveBlockTransfer = mkBTransfer live
>   where
>     live :: StmtM e x -> Fact x LiveBlock -> LiveBlock

|Bind|, |CaseM| and |Done| are treated nearly identically. We look in
the tails and find all referenced blocks. Those are added to the
accumulated |liveBlocks| set. Entry labels just transfer the
accumulated set untouched.
\restorecolumns

>     live (Bind v tail) liveBlocks = Set.fromList (tailDest tail) 
>                                     `Set.union` liveBlocks
>     live (CaseM _ alts) liveBlocks = Set.unions (map (Set.fromList . tailDest . altE) 
>                                                  alts ++ mapElems liveBlocks)
>     live (Done _ _ tail) liveBlocks =  Set.unions (Set.fromList (tailDest tail) : 
>                                                mapElems liveBlocks)
>     live (BlockEntry _ l _) liveBlocks = liveBlocks
>     live (CloEntry _ l _ _) liveBlocks = liveBlocks


The facts gathered are converted to a map of blocks to predecessors. |BlockPredecessors|
implements this map using the |Dest| type, which uniquely names a block.

> type BlockPredecessors = Map Dest [Dest]


The map is built by |findBlockPreds|. To get |LiveBlock| facts
(indexed by label) from Hoopl, we pattern match on the result of
|analyzeAndRewriteBwd|. That value, |f|, is then manipulated to get a
map of blocks to their predecessors. We also must be sure that we do
NOT eliminate top-level functions (which have no predecessors, but we
don't want to eliminate them!). The |tops| argument makes sure we know
which blocks those are.
\savecolumns

> findBlockPreds :: [Name] -> ProgM C C -> BlockPredecessors
> findBlockPreds tops body = runSimple $ do
>     (_, f, _) <- analyzeAndRewriteBwd bwd (JustC labels) body initial
>     return $ Map.fromList (catMaybes (map convert (mapToList f)))
>   where

To indicate to Hoopl that we are doing a backwards, analysis only,
pass, we build a |BwdPass| value with a no-op rewrite function that
Hoopl provides, |noBwdRewrite|. Our fact lattice is based on
|LiveBlock| and will union facts together until no more
changes occur. The transfer function, |liveBlockTransfer| is defined 
above.
\restorecolumns

>     bwd = BwdPass { bp_lattice = liveBlockLattice
>                   , bp_transfer = liveBlockTransfer
>                   , bp_rewrite = noBwdRewrite }
>     liveBlockLattice :: DataflowLattice LiveBlock
>     liveBlockLattice = DataflowLattice { fact_name = "Live blocks"
>                                        , fact_bot = Set.empty
>                                        , fact_join = extend }
>     extend _ (OldFact old) (NewFact new) = 
>       (changeIf (not (Set.null (Set.difference new old)))
>       , new)
> 

The remaining functions for |findBlockPreds| take care of converting our facts
to a |BlockPredecessors| value.
\restorecolumns

>     convert (label, set) = case blockOfLabel body label of
>                                  Just (dest, _) -> Just (dest, Set.toList set)
>                                  _ -> Nothing
>     labels = entryLabels body
>     initial = mkFactBase (bp_lattice bwd) 
>               (zip labels(repeat (Set.fromList (topLabels body))))
>     topLabels :: ProgM C C -> [Dest]
>     topLabels = filter (\(n, l) -> n `elem` tops) . map fst . allBlocks


To remove dead blocks, we re-implement a small part of Hoopl's interleaved, 
iterative analysis and rewriting. |deadBlocks| uses |findBlockPreds| to find
predecessors for all blocks. |removeOrphans| eliminates any blocks without
predecessors (that are not top-level blocks, of course). It will  return |SomeChange|
and the new graph if any blocks were eliminated. As long as |SomeChange| is returned,
|deadBlocks| will continue to execute, looking for more blocks to execute. When no
more changes occure, the rewritten graph is returned.

> deadBlocks :: [Name] -> ProgM C C -> ProgM C C
> deadBlocks tops prog = 
>   case removeOrphans (liveSet prog) prog of
>     (SomeChange, prog') -> deadBlocks tops prog'
>     _ -> prog
>   where
>     liveSet = Set.fromList . concat . Map.elems . findBlockPreds tops
> 
>     removeOrphans :: LiveBlock 
>                   -> ProgM C C 
>                   -> (ChangeFlag, ProgM C C)
>     removeOrphans live = foldl (remove live) 
>                                (NoChange, emptyClosedGraph) . 
>                                allBlocks
> 
>     remove :: LiveBlock 
>                  -> (ChangeFlag, ProgM C C) 
>                  -> (Dest, Block StmtM C C) 
>                  -> (ChangeFlag, ProgM C C)
>     remove live (flag, prog) (dest, block) 
>       | dest `Set.member` live = (flag, blockGraph block |*><*| prog)
>       | otherwise = (SomeChange, prog)
> 
