%if False

> {-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
>   , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}
> module DeadBlocks (deadBlocks, BlockReferrers, findBlockReferrers)
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
> import Debug.Trace (trace)
> 
> import Compiler.Hoopl
> 
> import Util
> import MIL
> import Live
>

%endif

We eliminate dead blocks by finding those with no referrers -- that
is, any block that is not called by another block (using |Goto|) or
whose address is not stored in a closure or thunk can be eliminated.

The |BlockReferrers| map gives the blocks that refer to a given
block. That is, the key is a block and the associated values are all
the blocks that refer to the key. If no blocks refer to a
block, the set will be empty.

> type BlockReferrers = Map Dest (Set Dest)

We start by using |allBlocks| to convert the program to a list of
blocks. We use |foldl| to apply |addBlock| to that list. The result is
our |BlockReferrers| value. 

> findBlockReferrers :: ProgM C C -> BlockReferrers
> findBlockReferrers = foldl addBlock Map.empty . allBlocks
>   where

The |addBlock| function folds over the statements in the current block
using the |addReferrer| function to find all the blocks referenced by
the current block. |addReferrer| adds the current block to the set of
referrers for each block mentioned in the current block. |addRef|
takes care of adding the current block to each mentioned block's
referrer set.

Blocks are only added to the BlockReferrer set when they are
referenced by another block. Therefore, any block in the
BlockReferrers set must have at least one referrer.

>     addBlock :: BlockReferrers -> (Dest, Block StmtM C C) -> BlockReferrers
>     addBlock refMap (dest, block) = foldFwdBlock (addReferrer dest) refMap block

>     addReferrer :: Dest -> (forall e x. BlockReferrers -> StmtM e x -> BlockReferrers)
>     addReferrer referrer refMap (Bind _ tail) = foldl (addRef referrer) refMap (tailDest tail)
>     addReferrer referrer refMap (CaseM _ alts) = foldl (addRef referrer) refMap (concatMap (tailDest . altE) alts) 
>     addReferrer referrer refMap (Done _ _ tail) = foldl (addRef referrer) refMap (tailDest tail) 
>     addReferrer referrer refMap (BlockEntry _ _ _) = refMap
>     addReferrer referrer refMap (CloEntry _ _ _ _) = refMap

>     addRef :: Dest -> BlockReferrers -> Dest -> BlockReferrers
>     addRef referrer refs reference = Map.insertWith Set.union reference (Set.singleton referrer) refs
 
To remove dead blocks, we re-implement a small part of Hoopl's
interleaved, iterative analysis and rewriting. |deadBlocks| uses
|findBlockReferrers| to find predecessors for all
blocks. |removeOrphans| eliminates any blocks without predecessors
(that are not top-level blocks, of course). It will return
|SomeChange| and the new graph if any blocks were eliminated. As long
as |SomeChange| is returned, |deadBlocks| will continue to execute,
looking for more blocks to remove. When no more changes occur, the
rewritten graph is returned.

> deadBlocks :: [Name] -> ProgM C C -> ProgM C C
> deadBlocks tops prog = 
>   case removeOrphans (liveSet prog) prog of
>     (SomeChange, prog') -> deadBlocks tops prog'
>     _ -> prog
>   where
>     -- Live blocks are those with at least one refererr, or which
>     -- are named in the tops list (i.e., a top-level function).
>     liveSet :: ProgM C C -> Set Dest
>     liveSet = Set.fromList . Map.keys . findBlockReferrers 

>     removeOrphans :: Set Dest
>                   -> ProgM C C 
>                   -> (ChangeFlag, ProgM C C)
>     removeOrphans live = foldl (remove live) 
>                                (NoChange, emptyClosedGraph) . 
>                                allBlocks
> 
>     remove :: Set Dest
>                  -> (ChangeFlag, ProgM C C) 
>                  -> (Dest, Block StmtM C C) 
>                  -> (ChangeFlag, ProgM C C)
>     remove live (flag, prog) (dest@(name, _), block) 
>       | dest `Set.member` live || name `elem` tops = (flag, blockGraph block |*><*| prog)
>       | otherwise = (SomeChange, prog)
> 
