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

> data CloDest = CloDest Dest [Name]

%endif
%if False

>             deriving (Eq, Show)

Indicates if the given name holds an allocated
closure or an unknown value.

%endif
%if includeAll || includeTypes

> type CollapseFact = Map Name (WithTop CloDest)

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

%endif
%if includeAll || includeTransfer

> collapseTransfer :: FwdTransfer StmtM CollapseFact
> collapseTransfer = mkFTransfer t
>   where
>     t :: StmtM e x -> CollapseFact -> Fact x CollapseFact
>     t (Bind v (Closure dest args)) facts = 
>       Map.insert v (PElem (CloDest dest args)) 
>                    (kill v facts)
>     t (Bind v _) facts = Map.insert v Top (kill v facts)
>     t (CaseM _ _) facts = mkFactBase collapseLattice []
>     t (Done _ _ _) facts = mkFactBase collapseLattice []
>     t (BlockEntry _ _ _) facts = facts
>     t (CloEntry _ _ _ _) facts = facts
>   
>     kill :: Name -> Map Name (WithTop CloDest) -> Map Name (WithTop CloDest)
>     kill v = Map.filter (not . using v) 
>
>     using :: Name -> WithTop CloDest -> Bool
>     using _ Top = False
>     using var (PElem (CloDest _ vars)) = var `elem` vars
>   

%endif
%if includeRewrite || includeAll 

> collapseRewrite :: FuelMonad m => Map Label DestOf 
>                    -> FwdRewrite m StmtM CollapseFact
> collapseRewrite blocks = iterFwdRw (mkFRewrite rewriter)
>   where
>     rewriter :: FuelMonad m => forall e x. StmtM e x -> CollapseFact 
>                 -> m (Maybe (ProgM e x))
>     rewriter (Done n l (Enter f x)) col = done n l (collapse col f x)
>     rewriter (Bind v (Enter f x)) col = bind v (collapse col f x)
>     rewriter _ _ = return Nothing
>                    
>     collapse :: CollapseFact -> Name -> Name -> Maybe TailM
>     collapse facts f x =       
>       case Map.lookup f facts of
>         Just (PElem (CloDest dest@(_, l) vs)) -> 
>           case Map.lookup l blocks of
>             Just (Jump dest uses) -> 
>               Just (Goto dest (fromUses uses (vs ++ [x])))
>             Just (Capture dest usesArg) ->
>               Just (Closure dest 
>                     (if usesArg then vs ++[x] else vs))
>             _ -> Nothing
>         _ -> Nothing

%endif
%if False

Idxs is a list of positions which represent
how a Goto used the arguments given in a CloEntry. We
take local arguments and re-order them according to
the positions given.

%endif
%if includeRewrite || includeAll

>     fromUses :: [Int] -> [Name] -> [Name]
>     fromUses idxs args = map (args !!) idxs

%endif
%if includeAll || includeLattice

> collapseLattice :: DataflowLattice CollapseFact
> collapseLattice = DataflowLattice { fact_name = "Closure collapse"
>                                   , fact_bot = Map.empty
>                                   , fact_join = joinMaps (toJoin lub) }
>
> toJoin :: (a -> a -> (ChangeFlag, a)) 
>        -> (Label -> OldFact a -> NewFact a -> (ChangeFlag, a))
> toJoin f = 
>   let f' _ (OldFact o) (NewFact n) = f o n
>   in f' 

> lub :: WithTop CloDest -> WithTop CloDest -> (ChangeFlag, WithTop CloDest)
> lub old new = 
>   if old == new 
>    then (NoChange, new)
>    else (SomeChange, Top)

%endif