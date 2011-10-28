%if False

> {-# LANGUAGE RankNTypes, GADTs #-}
> module Uncurry (collapse)
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
> import Live

Closure/App collapse (aka "Beta-Fun" from "Compiling with
Continuations, Continued" section 2.3)

  f1 (t) {x, y,z} : g(x,y,z,t)
  ...
  h1:
    v0 <- closure f1 {x,y,z}
    v1 <- v0 @@ w 
   ==>
  h1:
    v1 <- g(x,y,z,w)  


Associates a label with the destination which it either captures
(Closure) or jumps to (Goto). We store the index at which the
argument to a closure will be stored, if it is used. For goto,
we store the variables passed as positions from teh arguments
given to the block. 

%endif
%if includeAll || includeTypes

> data DestOf = Jump Dest [Int] | Capture Dest Bool

%endif
%if False

>               deriving (Eq, Show)

Stores destination and arguments for a 
closure value. Mostly to remove annoying
GADT type variables.

%endif
%if includeAll || includeTypes

> data CloVal = CloVal Dest [Name]

%endif
%if False

>             deriving (Eq, Show)

Indicates if the given name holds an allocated
closure or an unknown value.

%endif
%if includeAll || includeTypes

> type CollapseFact = Map Name (WithTop CloVal) 

%endif
%if False

Need to track variables stored in a closure as well

 
Collapse closure allocations - when we can tell a variable holds
a closure, and that closure only allocates another closure or jumps
to a block, then avoid that extra step and directly allocate the
closure or jump to the block.

%endif
%if includeAll

> collapse :: ProgM C C -> ProgM C C
> collapse body = deadCode . runSimple $ do
>       (p, _, _) <- analyzeAndRewriteFwd fwd (JustC labels) body initial
>       return p
>   where
>     labels = entryLabels body
>     initial = mapFromList (zip labels (repeat Map.empty))
>     -- debug = debugFwdJoins trace (const True)
>     fwd = FwdPass { fp_lattice = collapseLattice
>                   , fp_transfer = collapseTransfer 
>                   , fp_rewrite = collapseRewrite (destinations labels) }
>     destinations = Map.fromList . catMaybes . map (uncurry destOf) . catMaybes .  map (blockOfLabel body)
>     destOf :: Dest -> Block StmtM C C -> Maybe (Label, DestOf)
>     destOf (_, l)  block = 
>       case blockToNodeList' block of
>         (JustC (CloEntry _ _ args arg), _, JustC (Done _ _ (Goto d uses))) -> 
>           Just (l, Jump d (mapUses uses (args ++ [arg])))
>         (JustC (CloEntry _ _ _ arg), _, JustC (Done _ _ (Closure d args))) -> 
>           Just (l, Capture d (arg `elem` args))
>         _ -> Nothing
>     mapUses :: [Name] -> [Name] -> [Int]
>     mapUses uses args = catMaybes (map (`elemIndex` args) uses)
> 
> collapseTransfer :: FwdTransfer StmtM CollapseFact
> collapseTransfer = mkFTransfer fw
>   where
>     fw :: StmtM e x -> CollapseFact -> Fact x CollapseFact
>     fw (Bind v (Closure dest args)) bound = Map.insert v (PElem (CloVal dest args)) bound
>     fw (Bind v _) bound = Map.insert v Top bound
>     fw (CaseM _ alts) bound = mkFactBase collapseLattice []
>     fw (Done _ _ _) bound = mkFactBase collapseLattice []
>     fw (BlockEntry _ _ _) f = f
>     fw (CloEntry _ _ _ _) f = f

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
>         Just (PElem (CloVal dest@(_, l) vs)) -> 
>           case l `Map.lookup` blocks of
>             Just (Jump dest uses) -> Just (Goto dest (fromUses uses (vs ++ [x])))
>             Just (Capture dest True) -> Just (Closure dest (vs ++ [x]))
>             Just (Capture dest _) -> Just (Closure dest vs)
>             _ -> Nothing
>         _ -> Nothing
>                             
>     -- Idxs is a list of positions which represent
>     -- how a Goto used the arguments given in a CloEntry. We
>     -- take local arguments and re-order them according to
>     -- the positions given.
>     fromUses :: [Int] -> [Name] -> [Name]
>     fromUses idxs args = map (args !!) idxs

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

%endif