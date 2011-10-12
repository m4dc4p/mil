%if False

> {-# LANGUAGE GADTs, RankNTypes #-}
> 
> module DeadCodeC 
> where

%endif
%if includeAll

> import Data.List (nub)
> import Data.Set (Set, union, unions, (\\)
>                  , singleton, delete, member)
> import Data.Map (Map)
> import qualified Data.Set as Set
> import qualified Data.Map as Map
> import Compiler.Hoopl

%endif
%if includeAst || includeAll

> data CStmt e x where
>   Entry :: Label -> CStmt C O
>   Assign :: Var -> CExpr -> CStmt O O
>   Call :: Var -> [CExpr] -> CStmt O O
>   Return :: CStmt O C
>
> data CExpr = Const Int 
>   | Add CExpr CExpr 
>   | Var Var 
>   | String String
>
> type Var = String

%endif
%if nonLocalInst || includeAll

> instance NonLocal CStmt where
>   entryLabel (Entry l) = l
>   successors _ = []

%endif
%if buildFoo || includeAll

> foo :: Label -> Graph CStmt C C
> foo l = mkFirst (Entry l) <*> 
>       mkMiddle (Assign "c" (Const 4)) <*>
>       mkMiddle (Assign "a" (Add (Var "c") (Const 1))) <*>
>       mkMiddle (Call "printf" [String "%d", Var "c"]) <*>
>       mkMiddle (Assign "a" (Add (Var "c") (Const 1))) <*>
>       mkLast Return

%endif
%if latticeDef || includeAll

> type Live = Set Var
>
> meet :: Label -> OldFact Live 
>         -> NewFact Live 
>         -> (ChangeFlag, Live)
> meet _ (OldFact old) (NewFact new) = 
>   (changeIf (old /= new), old `union` new)
>
> lattice :: DataflowLattice Live
> lattice = DataflowLattice { 
>       fact_name = "Liveness"
>     , fact_bot = Set.empty
>     , fact_join = meet }

%endif
%if includeLiveness || includeAll

> liveness :: BwdTransfer CStmt Live
> liveness = mkBTransfer transfer
>   where 
>     transfer :: forall e x. CStmt e x -> Fact x Live -> Live {-"\label{hoopl_eg_transfer}"-}
>     transfer (Entry _) f = Set.empty {-"\label{hoopl_eg_transfer_entry}"-}
>     transfer (Assign var expr) f = var `delete` (f `union` (uses expr)) {-"\label{hoopl_eg_transfer_assign}"-}
>     transfer (Call _ exprs) f = f `union` unions (map uses exprs) {-"\label{hoopl_eg_transfer_call}"-}
>     transfer Return _ = Set.empty {-"\label{hoopl_eg_transfer_return}"-}
>     
> uses :: CExpr -> Set Var {-"\label{hoopl_eg_transfer_uses}"-}
> uses (Add e1 e2) = uses e1 `union` uses e2
> uses (Var v) = singleton v
> uses _ = Set.empty

%endif

%if includeRewrite

> eliminate :: FuelMonad m => BwdRewrite m CStmt Live
> eliminate = mkBRewrite rewrite
>   where
>     rewrite :: FuelMonad m => forall e x. CStmt e x 
>                -> Fact x Live -> m (Maybe (Graph CStmt e x))
>     rewrite (Entry _) _ = return Nothing
>     rewrite (Assign var exprs) f =
>       if var `member` f
>        then return Nothing
>        else return (Just emptyGraph)
>     rewrite (Call _ _) _ = return Nothing
>     rewrite Return _ = return Nothing
>       

%endif
%if includeAll

> deadCode :: Graph CStmt C C -> Graph CStmt C C
> deadCode program = runSimpleUniqueMonad $ runInfinite $ do
>     (prog, _, _) <- analyzeAndRewriteBwd opt (JustC entryPoints) program initialFacts
>     return prog
>   where
>     opt = BwdPass { bp_lattice = lattice
>                   , bp_transfer = liveness 
>                   , bp_rewrite = eliminate }
>
>     entryPoints = case program of 
>       (GMany _ blocks _) -> map entry (mapElems blocks)
>
>     entry :: Block CStmt C x -> Label
>     entry (BFirst (Entry l)) = l
>
>     initialFacts = mkFactBase lattice (zip entryPoints (repeat Set.empty))

%endif