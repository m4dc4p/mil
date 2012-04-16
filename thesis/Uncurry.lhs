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
%if includeCollapse || includeAll

> collapse :: ProgM C C -> ProgM C C
> collapse program = runSimple $ do {-"\hslabel{run}"-}
>       (p, _, _) <- analyzeAndRewriteFwd fwd (JustC labels) program initial {-"\hslabel{analyze}"-}
>       return p
>   where
>     labels :: [Label]
>     labels = entryLabels program {-"\hslabel{labels}"-}
>
>     initial :: FactBase CollapseFact
>     initial = mapFromList (zip labels (repeat Map.empty)) {-"\hslabel{initial}"-}
>
>     fwd :: FwdPass SimpleFuelMonad Stmt CollapseFact
>     fwd = FwdPass { fp_lattice = collapseLattice {-"\hslabel{fwd}"-}
>                   , fp_transfer = collapseTransfer blockArgs
>                   , fp_rewrite = collapseRewrite (destinations labels) }
>     
>     blockArgs :: Map Label [Name]
>     blockArgs = Map.fromList [(l, args) | (_, BlockEntry _ l args) <- entryPoints program]
>
>     destinations :: [Label] -> Map Label DestOf
>     destinations = Map.fromList . catMaybes . {-"\hslabel{destinations}"-}
>                    map (uncurry destOf) . catMaybes .  map (blockOfLabel program)
>
>     destOf :: Dest -> Block Stmt C C -> Maybe (Label, DestOf)
>     destOf (_, l)  block = {-"\hslabel{destOf}"-}
>       case blockToNodeList' block of
>         (JustC (CloEntry _ _ args arg), _, JustC (Done _ _ (Goto d uses))) -> 
>           Just (l, Jump d (mapUses uses (args ++ [arg])))
>         (JustC (CloEntry _ _ _ arg), _, JustC (Done _ _ (Closure d args))) -> 
>           Just (l, Capture d (arg `elem` args))
>         _ -> Nothing
>     
>     mapUses :: [Name] -> [Name] -> [Int]
>     mapUses uses args = catMaybes (map (`elemIndex` args) uses) {-"\hslabel{mapUses}"-}

%endif
%if includeAll || includeTransfer

> collapseTransfer :: Map Label [Name] -> FwdTransfer Stmt CollapseFact
> collapseTransfer blockArgs = mkFTransfer t
>   where
>     t :: Stmt e x -> CollapseFact -> Fact x CollapseFact
>     t (Bind v (Closure dest args)) facts = {-"\hslabel{closure}"-}
>       Map.insert v (PElem (CloDest dest args)) 
>                    (kill v facts)
>     t (Bind v _) facts = Map.insert v Top (kill v facts) {-"\hslabel{rest}"-}
>     t (Case _ alts) bound = 
>       mkFactBase collapseLattice [(dest, renameAlt bound binds (blockArgs ! dest) args) | 
>                                   (Alt _ binds (Goto (_, dest) args)) <- alts] 
>     t (Done _ _ (Goto (_, dest) args)) bound = 
>       mapSingleton dest (renameBound args (blockArgs ! dest) bound)
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
>     renameAlt origFacts binds newNames origNames = 
>       -- Remove any facts shadowed by this alternative's bindings.
>       -- Includes facts that use a shadowed variable, as well
>       -- as facts about a shadowed variable.
>       let remainingFacts = 
>               foldr (\v f -> kill v f) 
>                 (Map.filterWithKey (\v _ -> v `elem` binds) origFacts) binds
>       in renameBound origNames newNames remainingFacts
>                   
>     -- Rename variables in CollapseFact according to
>     -- the names used by the destination block.
>     renameBound :: [Name] -> [Name] -> CollapseFact -> CollapseFact
>     renameBound origNames newNames = Map.mapKeys (rename origNames newNames) 
>
>     rename :: [Name] -> [Name] -> Name -> Name
>     rename args blockArgs arg  = 
>       case arg `elemIndex` args of
>         Just i -> blockArgs !! i -- rename to block argument
>         _ -> arg -- don't rename
>
>     -- A candidate for renaming is a var that is not shadowed and appears
>     -- in the args list. The ignored argument just makes this easier to
>     -- use with Map.filterWithKey.
>     candidate :: [Name] -> [Name] -> Name -> a -> Bool
>     candidate shadows args var _ = not (var `elem` shadows) && var `elem` args

%endif
%if includeRewrite || includeAll 

> collapseRewrite :: FuelMonad m => Map Label DestOf 
>                    -> FwdRewrite m Stmt CollapseFact
> collapseRewrite blocks = iterFwdRw (mkFRewrite rewriter) {-"\hslabel{top}"-}

%endif
%if includeAll

>   where

%endif
%if includeRewriteImpl || includeAll

>     rewriter :: FuelMonad m => forall e x. Stmt e x -> CollapseFact 
>                 -> m (Maybe (ProgM e x))
>     rewriter (Done n l (Enter f x)) facts = done n l (collapse facts f x) {-"\hslabel{done}"-}
>     rewriter (Bind v (Enter f x)) facts = bind v (collapse facts f x) {-"\hslabel{bind}"-}
>     rewriter _ _ = return Nothing {-"\hslabel{rest}"-}
>                    
>     collapse :: CollapseFact -> Name -> Name -> Maybe Tail
>     collapse facts f x =       
>       case Map.lookup f facts of
>         Just (PElem (CloDest dest@(_, l) vs)) -> {-"\hslabel{collapse_clo}"-}
>           case Map.lookup l blocks of
>             Just (Jump dest uses) -> {-"\hslabel{collapse_jump}"-}
>               Just (Goto dest (fromUses uses (vs ++ [x])))
>             Just (Capture dest usesArg) -> {-"\hslabel{collapse_capt}"-}
>               Just (Closure dest 
>                     (if usesArg then vs ++[x] else vs))
>             _ -> Nothing
>         _ -> Nothing
>
>     fromUses :: [Int] -> [Name] -> [Name]
>     fromUses idxs args = map (args !!) idxs

%endif
%if False

Idxs is a list of positions which represent
how a Goto used the arguments given in a CloEntry. We
take local arguments and re-order them according to
the positions given.

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