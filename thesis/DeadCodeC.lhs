%if False

> {-# LANGUAGE GADTs, RankNTypes #-}
> 
> module DeadCodeC 
> where

%endif
%if includeAll

> import Data.List (nub)
> import Data.Set (Set, union, unions, (\\)
>                  , singleton, delete)
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
>     transfer (Entry _) f = f {-"\label{hoopl_eg_transfer_entry}"-}
>     transfer (Assign var expr) f = var `delete` (f `union` (vars expr)) {-"\label{hoopl_eg_transfer_assign}"-}
>     transfer (Call _ exprs) f = f `union` unions (map vars exprs) {-"\label{hoopl_eg_transfer_call}"-}
>     transfer Return f = unions (mapElems f) {-"\label{hoopl_eg_transfer_return}"-}
>     
>     vars :: CExpr -> Set Var {-"\label{hoopl_eg_transfer_vars}"-}
>     vars (Add e1 e2) = vars e1 `union` vars e2
>     vars (Var v) = singleton v
>     vars _ = Set.empty

%endif
%if includeAll

> deadCode :: Graph CStmt C C -> Graph CStmt C C
> deadCode = undefined

%endif