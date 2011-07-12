%if False

> {-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
>   , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}
> module DeadBlocks (deadBlocks, BlockPredecessors)
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

Our analysis finds all the live blocks in the program. A block |p| is
live if block |b| explicitly calls the block using a |Goto p|
statement or returns a reference to it in a |Closure| or |Thunk|
value. Our type |LiveBlocks| maps referred blocks to their
referrers. Each block will appear in the map. If no other blocks refer
to a given block, the list stored with that block will be empty.

> type ReferrencedBlocks = Map Dest [Dest]

To find live blocks, we iterate over the statements in each block and
discover all explicit block references in |Tail| expressions (as
returned by the |tailDest| function). The set of these references
are the live blocks.

> findBlockReferences :: ProgM C C -> ReferrencedBlocks
> findBlockReferences body = undefined -- foldl add Map.empty . allBlocks

>   where
>     add refMap (dest, block) = 
>       let refs = nub . foldlBlock findRefs []
>       in Map.insert dest (refs block) refMap

>     findRefs :: ReferrencedBlocks -> StmtM e x -> ReferrencedBlocks
>     findRefs liveBlocks (Bind v tail) = tailDest tail ++ liveBlocks
>     findRefs liveBlocks (CaseM _ alts) = concat (liveBlocks : map (tailDest . altE) alts)
>     findRefs liveBlocks (Done _ _ tail) =  liveBlocks ++ tailDest tail
>     findRefs liveBlocks (BlockEntry _ l _) = liveBlocks
>     findRefs liveBlocks (CloEntry _ l _ _) = liveBlocks

To remove dead blocks, we re-implement a small part of Hoopl's interleaved, 
iterative analysis and rewriting. |deadBlocks| uses |findBlockReferences| to find
references for all blocks. |removeOrphans| eliminates any blocks without
references (that are not top-level blocks, of course). It will  return |SomeChange|
and the new graph if any blocks were eliminated. As long as |SomeChange| is returned,
|deadBlocks| will continue to execute, looking for more blocks to eliminate. When no
more changes occure, the rewritten graph is returned.

> deadBlocks :: Set Dest -> ProgM C C -> ProgM C C
> deadBlocks tops prog = {-# SCC "deadBlocksQ" #-}
>   case removeOrphans (concat . Map.elems . findBlockPreds $ prog) prog of
>     (SomeChange, prog') -> deadBlocks tops prog'
>     _ -> prog
>   where
>     removeOrphans :: LiveBlocks 
>                   -> ProgM C C 
>                   -> (ChangeFlag, ProgM C C)
>     removeOrphans live = foldl (remove live) 
>                                (NoChange, emptyClosedGraph) . 
>                                allBlocks
> 
>     remove :: LiveBlocks 
>                  -> (ChangeFlag, ProgM C C) 
>                  -> (Dest, Block StmtM C C) 
>                  -> (ChangeFlag, ProgM C C)
>     remove live (flag, prog) (dest, block) =
>       case Map.lookup dest live of
>         Just [] -> 
>       | dest `Set.member` live || dest `Set.member` tops = (flag, blockGraph block |*><*| prog)
>       | otherwise = (SomeChange, prog)
> 
