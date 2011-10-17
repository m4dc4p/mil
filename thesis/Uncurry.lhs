> {-# LANGUAGE RankNTypes, GADTs #-}
> module Uncurry
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
> import Debug.Trace
>   
> import Compiler.Hoopl
> 
> import Util
> import MIL
> 
> -- Closure/App collapse (aka "Beta-Fun" from "Compiling with
> -- Continuations, Continued" section 2.3)
> --
> --   f1 (t) {x, y,z} : g(x,y,z,t)
> --   ...
> --   h1:
> --     v0 <- closure f1 {x,y,z}
> --     v1 <- v0 @ w 
> --    ==>
> --   h1:
> --     v1 <- g(x,y,z,w)  
> -- 
> 
> -- | Associates a label with the destination which it either captures
> -- (Closure) or jumps to (Goto). We store the index at which the
> -- argument to a closure will be stored, if it is used.
> data DestOf = Jump Dest 
>             | Capture Dest (Maybe Int)
>               deriving (Eq, Show)
> 
> -- | Stores destination and arguments for a 
> -- closure value. Mostly to remove annoying
> -- GADT type variables.
> data CloVal = CloVal Dest [Name]
>             deriving (Eq, Show)
> 
> -- | Indicates if the given name holds an allocated
> -- closure or an unknown value.
> type CollapseFact = Map Name (WithTop CloVal) -- Need to track
>                                               -- variables stored in a
>                                               -- closure as well
> 
> -- | Collapse closure allocations - when we can tell a variable holds
> -- a closure, and that closure only allocates another closure or jumps
> -- to a block, then avoid that extra step and directly allocate the
> -- closure or jump to the block.
> collapse :: ProgM C C -> ProgM C C
> collapse body = runSimple $ do
>       (p, _, _) <- analyzeAndRewriteFwd fwd (JustC labels) body initial
>       return p
>   where
>     labels = entryLabels body
>     destinations = Map.fromList . catMaybes . map (destOf body) 
>     initial = mapFromList (zip labels (repeat (topFacts body)))
>     -- We determine if each top-level name only allocates
>     -- a closure or not, and use that as our initial facts.
>     topFacts :: ProgM C C -> CollapseFact
>     topFacts = Map.fromList . map factForBlock . allBlocks
>     -- Conceptually, all top-level labels hold a closure pointing to
>     -- the entry point of the procedure. We don't implement it
>     -- that way but the below will fake it for purposes of this
>     -- optimization. 
>     --
>     -- TODO: Filter the initial facts to top-level names only, the below
>     -- will create an entry for all labels.
>     factForBlock :: (Dest, Block StmtM C C) -> (Name, WithTop CloVal)
>     factForBlock (dest@(name, _), block) = (name, PElem (CloVal dest [])) 
>     destOf :: ProgM C C -> Label -> Maybe (Label, DestOf)
>     destOf body l = case blockOfLabel body l of
>                    Just (_,  block) ->
>                      case blockToNodeList' block of
>                        (JustC (CloEntry {}), [], JustC (Done _ _ (Goto d _))) -> Just (l, Jump d)
>                        (JustC (CloEntry _ _ _ arg), [], JustC (Done _ _ (Closure d args))) -> Just (l, Capture d (arg `elemIndex` args))
>                        _ -> Nothing
>                    _ -> Nothing
>     fwd = FwdPass { fp_lattice = collapseLattice
>                   , fp_transfer = collapseTransfer
>                   , fp_rewrite = collapseRewrite (destinations labels) }
> 
> collapseTransfer :: FwdTransfer StmtM CollapseFact
> collapseTransfer = mkFTransfer fw
>   where
>     fw :: StmtM e x -> CollapseFact -> Fact x CollapseFact
>     fw (Bind v (Closure dest args)) bound = Map.insert v (PElem (CloVal dest args)) bound
>     fw (Bind v _) bound = Map.insert v Top bound
>     fw s@(CaseM _ alts) bound = mkFactBase collapseLattice (zip (stmtSuccessors s) (repeat bound))
>     fw s@(Done _ _ _) bound = mkFactBase collapseLattice  (zip (stmtSuccessors s) (repeat bound))
>     fw (BlockEntry _ _ _) f = f
>     fw (CloEntry _ _ _ _) f = f
>     
> collapseRewrite :: FuelMonad m => Map Label DestOf -> FwdRewrite m StmtM CollapseFact
> collapseRewrite blocks = iterFwdRw (mkFRewrite rewriter)
>   where
>     rewriter :: FuelMonad m => forall e x. StmtM e x -> CollapseFact -> m (Maybe (ProgM e x))
>     rewriter (Done n l (Enter f x)) col = done n l (collapse col f x)
>     rewriter (Bind v (Enter f x)) col = bind v (collapse col f x)
>     rewriter _ _ = return Nothing
> 
>     collapse :: CollapseFact -> Name -> Name -> Maybe TailM
>     collapse col f x =       
>       case Map.lookup f col of
>         Just (PElem (CloVal dest@(_, l) vs)) -> -- Just (Closure dest (vs ++ [x]))
>           case l `Map.lookup` blocks of
>             Just (Jump dest) -> Just (Goto dest (vs ++ [x]))
>             Just (Capture dest (Just idx)) -> Just (Closure dest (insertAt vs idx x))
>             Just (Capture dest _) -> Just (Closure dest vs)
>             _ -> Nothing
>         _ -> Nothing
> 
> collapseLattice :: DataflowLattice CollapseFact
> collapseLattice = DataflowLattice { fact_name = "Closure collapse"
>                                   , fact_bot = Map.empty
>                                   , fact_join = joinMaps (extendJoinDomain extend) }
>   where
>     extend :: Label 
>            -> OldFact CloVal
>            -> NewFact CloVal
>            -> (ChangeFlag, WithTop CloVal)
>     extend _ (OldFact old) (NewFact new) 
>       | old == new = (NoChange, PElem new)
>       | otherwise = (SomeChange, Top)

