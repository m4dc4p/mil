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
> import Compiler.Hoopl hiding (Label, Fact)
> import qualified Compiler.Hoopl as Hoopl (Label, Fact)
> 
> import Util hiding (Var)
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

> type Label = Dest
> type Var = Name

%endif

%if includeAll || includeTypes

< data Clo = Clo Label [Var]
< type Label = (String, Hoopl.Label)
< type Var = String
< data DestOf = Jump Label [Int] | Capture Label Bool
< type Fact = Map Var (WithTop Clo)

%endif
%if False

> data DestOf = Jump Label [Int] | Capture Label Bool
>               deriving (Eq, Show)

Stores destination and arguments for a 
closure value. Mostly to remove annoying
GADT type variables.

> data Clo = Clo Label [Var]
>             deriving (Eq, Show)


Indicates if the given name holds an allocated
closure or an unknown value.

> type Fact = Map Var (WithTop Clo)

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
>     labels :: [Hoopl.Label]
>     labels = entryLabels program {-"\hslabel{labels}"-}
>
>     initial :: FactBase Fact
>     initial = mapFromList (zip labels (repeat Map.empty)) {-"\hslabel{initial}"-}
>     fwd :: FwdPass SimpleFuelMonad Stmt Fact
>     fwd = FwdPass { fp_lattice = collapseLattice {-"\hslabel{fwd}"-}
>                   , fp_transfer = collapseTransfer blockArgs
>                   , fp_rewrite = collapseRewrite (destinations labels) -- noFwdRewrite 
>                     }
>     
>     blockArgs :: Map Hoopl.Label [Var]
>     blockArgs = Map.fromList [(l, args) | (_, BlockEntry _ l args) <- entryPoints program]
>
>     destinations :: [Hoopl.Label] -> Map Hoopl.Label DestOf
>     destinations = Map.fromList . catMaybes . {-"\hslabel{destinations}"-}
>                    map (uncurry destOf) . catMaybes .  map (blockOfLabel program)
>
>     destOf :: Label -> Block Stmt C C -> Maybe (Hoopl.Label, DestOf)
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

%if False

>
>     debugFwdT = debugFwdTransfers trace (show . printStmtM) (\ _ _ -> True) fwd
>     debugFwdJ = debugFwdJoins trace (const True) fwd
>     
                
%endif

%endif
%if includeAll || includeTransfer

> collapseTransfer :: Map Hoopl.Label [Name] -> FwdTransfer Stmt Fact
> collapseTransfer blockParams = mkFTransfer transfer
>   where
>     transfer :: Stmt e x -> Fact -> Hoopl.Fact x Fact
>     transfer (BlockEntry _ _ _) facts = facts
>     transfer (CloEntry _ _ _ _) facts = facts
>     transfer (Bind v (Closure dest args)) facts 
>       | v `elem` args = Map.delete v facts' {-"\hslabel{closure1}"-}
>       | otherwise = Map.insert v (PElem (Clo dest args)) facts' {-"\hslabel{closure2}"-}
>       where facts' = kill v facts {-"\hslabel{closure_kill}"-}
>     transfer (Bind v _) facts = Map.insert v Top (kill v facts) {-"\hslabel{rest}"-}
>     transfer (Done _ _ (Goto (_, dest) args)) facts = mapSingleton dest facts' {-"\hslabel{goto1}"-}
>       where facts' = rename args (blockParams ! dest) (restrict facts args) {-"\hslabel{goto2}"-}
>     transfer (Case _ alts) facts = mkFactBase collapseLattice facts' {-"\hslabel{case_result}"-}
>       where facts' =  [(dest, rename args params trimmed) | {-"\hslabel{case_start}"-}
>                         (Alt _ binds (Goto (_, dest) args)) <- alts, {-"\hslabel{case_alts}"-}
>                         let  trimmed = trim (restrict facts args) binds {-"\hslabel{case_trimmed}"-}
>                              params = blockParams ! dest] {-"\hslabel{case_end}"-}
>     transfer (Done _ _ _) facts = mkFactBase collapseLattice []
>   
>     kill :: Name -> Fact -> Fact {-"\hslabel{kill}"-}
>     kill = Map.filter . keep
>
>     keep :: Name -> WithTop Clo -> Bool
>     keep _ Top = True
>     keep v (PElem (Clo _ vs)) = not (v `elem` vs)
>
>     restrict :: Fact -> [Var] -> Fact
>     restrict fact vs = Map.filterWithKey (\v _ -> v `elem` vs) fact
>                        
>     trim :: Fact -> [Var] -> Fact
>     trim fact vs = foldr Map.delete (foldr kill fact vs) vs
>                       
>     rename :: [Name] -> [Name] -> Fact -> Fact
>     rename args params = Map.mapKeys renameKey 
>       where renameKey v = maybe v (params !!) (v `elemIndex` args)

%endif
%if includeRewrite || includeAll 

> collapseRewrite :: FuelMonad m => Map Hoopl.Label DestOf 
>                    -> FwdRewrite m Stmt Fact
> collapseRewrite blocks = iterFwdRw (mkFRewrite rewriter) {-"\hslabel{top}"-}

%endif
%if includeAll

>   where

%endif
%if includeRewriteImpl || includeAll

>     rewriter :: FuelMonad m => forall e x. Stmt e x -> Fact 
>                 -> m (Maybe (ProgM e x))
>     rewriter (Done n l (Enter f x)) facts = done n l (collapse facts f x) {-"\hslabel{done}"-}
>     rewriter (Bind v (Enter f x)) facts = bind v (collapse facts f x) {-"\hslabel{bind}"-}
>     rewriter _ _ = return Nothing {-"\hslabel{rest}"-}
>                    
>     collapse :: Fact -> Name -> Name -> Maybe Tail
>     collapse facts f x =       
>       case Map.lookup f facts of
>         Just (PElem (Clo dest@(_, l) vs)) -> {-"\hslabel{collapse_clo}"-}
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

> collapseLattice :: DataflowLattice Fact
> collapseLattice = DataflowLattice { fact_name = "Closure collapse"
>                                   , fact_bot = Map.empty
>                                   , fact_join = joinMaps (toJoin lub) }
>
> toJoin :: (a -> a -> (ChangeFlag, a)) 
>        -> (Hoopl.Label -> OldFact a -> NewFact a -> (ChangeFlag, a))
> toJoin f = \ _ (OldFact o) (NewFact n) -> f o n 

> lub :: WithTop Clo -> WithTop Clo -> (ChangeFlag, WithTop Clo)
> lub (PElem (Clo l _)) new@(PElem (Clo l' _))
>   | l == l' = (NoChange, new)
>   | otherwise = (SomeChange, Top)
> lub Top _ = (NoChange, Top)
> lub _ _ = (SomeChange, Top)

%endif