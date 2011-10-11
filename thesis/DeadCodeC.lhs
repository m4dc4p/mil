%if False

> {-# LANGUAGE GADTs #-}
> 
> module DeadCodeC 
> where

%endif
%if includeAll

> import Compiler.Hoopl
> import Data.Set (Set, isSubsetOf, union)
> import Data.Map (Map)
> import qualified Data.Set as Set
> import qualified Data.Map as Map

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
> lattice :: DataflowLattice (Map Label Live)
> lattice = DataflowLattice { 
>       fact_name = "Liveness"
>     , fact_bot = Map.empty
>     , fact_join = joinMaps meet }

%endif
%if nonLocalInst || includeAll

> instance NonLocal CStmt where
>   entryLabel (Entry l) = l
>   successors _ = []

%endif

%if includeAll

> deadCode :: Graph CStmt C C -> Graph CStmt C C
> deadCode = undefined

%endif