> module Lambda1
>
> where
> 
> import Control.Monad.State (State(runState), get, put)
> import Text.PrettyPrint 

Some useful synonyms first:

> type Var = String
> type Fun = String
> type Env = [Var]

Define \lamA terms:

> data Expr = App Expr Expr
>   | Abs Var Expr
>   | Var Var
>   deriving (Eq, Show)

Our monadic language:

> data ExprM = Let Var [ExprM]
>   | Enter ClosureM Var
>   | VarM Var
>   deriving (Eq, Show)

> data ClosureM = ClosureM Fun [Var]
>   deriving (Eq, Show)

Compiling expressions to our monadic language:

> compExpr :: Env -> Expr -> Comp [ExprM]
> compExpr env (Var v) = return [VarM v]
> compExpr env (App e1 e2) = do
>   v1 <- fresh "v"
>   v2 <- fresh "v"
>   e1M <- compExpr env e1
>   e2M <- compExpr env e2
>   return [Let v1 e1M
>          , Let v2 e2M
>          , Enter (ClosureM v1 (free env e2)) v2]
> compExpr env (Abs v e1) = do
>   let env' = v : env
>   compExpr env' e1

Our compilation monad creates new names for 
us:

> type Comp = State Int
>
> fresh :: String -> Comp String
> fresh prefix = do
>   i <- get
>   put (i + 1)
>   return (prefix ++ show i)

``free'' returns the free variables in an
expression:

> free :: Env -> Expr -> [Var]
> free e ex = free' e ex
>   where
>     free' env (App e1 e2) = free' env e1 ++ free' env e2
>     free' env (Abs v e1) = free' (v : env) e1
>     free' env (Var v) 
>           | v `elem` env = []
>           | otherwise = [v]

> run :: Expr -> [ExprM]
> run expr = fst $ runState (compExpr [] expr) 0

> compose :: Expr
> compose = 
>   (Abs "f" 
>        (Abs "g"  
>             (Abs "x" (App (Var "f") (App (Var "g") (Var "x"))))))
>                               


> printM :: String -> [ExprM] -> String
> printM name prog = render $ text name <+> text "=" <+> printExprs prog
>
> printExprs :: [ExprM] -> Doc
> printExprs exprs = text "do" $+$ nest 2 (foldl ($+$) empty (map printExpr exprs))
> 
> printExpr :: ExprM -> Doc
> printExpr (Let var expr) = text "let" <+> text var <+> text "=" <+> printExprs expr
> printExpr (Enter (ClosureM f vs) arg) = 
>   text "clo <-" <+> text "closure" <+> text f <+> brackets (hcat $ punctuate comma (map text vs)) $+$
>   text "enter clo" <+> text arg
> printExpr (VarM v) = text v 