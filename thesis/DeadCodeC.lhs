%if False
> {-# LANGUAGE GADTs #-}
> 
> module DeadCodeC 

> where

> import Compiler.Hoopl
%endif

%if includeAst
> data CStmt e x where
>   Assign :: Var -> CExpr -> CStmt O O
>   Call :: Var -> [CExpr] -> CStmt O O
>   Return :: CStmt O C
>   Entry :: Label -> CStmt C O
>
> data CExpr = Const Int 
>   | Add CExpr CExpr 
>   | Var Var 
>   | String String
>
> type Var = String
%endif

%if False
> foo l = mkFirst (Entry l) <*> 
>       mkMiddle (Assign "c" (Const 4)) <*>
>       mkMiddle (Assign "a" (Add (Var "c") (Const 1))) <*>
>       mkMiddle (Call "printf" [String "%d", Var "c"]) <*>
>       mkMiddle (Assign "a" (Add (Var "c") (Const 1))) <*>
>       mkLast Return

> instance NonLocal CStmt where
>   entryLabel (Entry l) = l
>   successors _ = []

> deadCode :: Graph CStmt C C -> Graph CStmt C C
> deadCode = undefined
%endif