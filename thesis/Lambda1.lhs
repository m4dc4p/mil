> {-# LANGUAGE NoImplicitPrelude #-}
> module Lambda1
>
> where
> 
> import Control.Monad.State (State(runState), get, put)
> import Text.PrettyPrint 
> import Prelude hiding (abs, flip, succ)

To compile a program, give it to the run function:

> run :: Prog -> IO ()
> run = putStrLn . printM . compile

Some functions. A helper for defining abstractions first:

> abs :: Var -> (Expr -> Expr) -> Expr
> abs n body = Abs n (body (Var n))

Then our friends the Church numerals. Starting with zero:

> zero :: Expr
> zero = abs "s" $ \s -> 
>        abs "z" $ \z -> z

We can define successor:

> succ :: Expr -> Expr
> succ n = abs "n" $ \n -> 
>        abs "s" $ \s -> 
>        abs "z" $ \z -> App s (App (App n s) z)

A program to calculate three:

> three :: Prog
> three = [("three", succ (succ (succ zero)))]

Some other classics:

then the compose function:

> compose :: Prog 
> compose = [("compose", def)]
>   where
>     def = abs "f" $ \f -> 
>           abs "g" $ \g -> 
>           abs "x" $ \x ->
>           App f (App g x)

Flip:

> flip :: Prog
> flip = [("flip", def)]
>   where
>     def = abs "f" $ \f ->
>           abs "a" $ \a ->
>           abs "b" $ \b ->
>           App (App f b) a

Now we define the language used above. Some useful synonyms first:

> type Var = String
> type Fun = String
> type Env = [Var]

Define \lamA terms:

> type Prog = [Def]
> type Def = (Fun, Expr)

> data Expr = App Expr Expr
>   | Abs Var Expr
>   | Var Var
>   deriving (Eq, Show)

Our monadic language. Top-level definitions have  a name, list of arguments
and a body:

> type ProgM = [DefM]
> type DefM = (Fun, BodyM)

The body of each definition can capture a variable and put it in
a closure (``Capture'') or be a block of real code (``BlockM''):

> data BodyM = Capture [Var] Var BodyM
>   | BlockM [Var] [ExprM]
>   deriving (Eq, Show)

Expressions can define a new value (``Let''), enter a closure (``Enter'') or
return a value from the environment (``VarM'')

> data ExprM = Let DefM
>   | Enter ClosureM Var
>   | VarM Var
>   deriving (Eq, Show)

Finally, a closure points to a function and carries a number of
variables around:

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
>   return [Let (v1, BlockM [] e1M)
>          , Let (v2, BlockM [] e2M)
>          , Enter (ClosureM v1 (free env e2)) v2]
> compExpr env (Abs v e1) = do
>   expr <- compExpr (v : env) e1
>   f <- fresh "f"
>   return [Let (f, BlockM [v] expr)]

> compProg :: Prog -> Comp [DefM]
> compProg ((name, def) : ds) = do
>   body <- compExpr [] def
>   rest <- compProg ds
>   return $ (name, BlockM [] body) : rest
> compProg [] = return []

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
>                         
> compile :: Prog -> [DefM]
> compile prog = fst $ runState (compProg prog) 0
>                


Utility functions for printing:

> printM :: ProgM -> String
> printM prog = render $ vcat' (map printDef prog)
>
> printDef :: DefM -> Doc
> printDef (name, BlockM vars body) = def <+> printExprs nesting body
>   where
>     def = text name <> parens (hcat $ punctuate comma (map text vars)) <+> 
>                        text "=" 
>     nesting = length (render def) 

> printExprs :: Int -> [ExprM] -> Doc
> printExprs nesting exprs = text "do" $+$ nest (nesting * (-1)) (vcat' (map printExpr exprs))
> 
> printExpr :: ExprM -> Doc
> printExpr (Let def) = text "let" <+> printDef def
> printExpr (Enter (ClosureM f vs) arg) = 
>   text "clo <-" <+> text "closure" <+> text f <+> brackets (hcat $ punctuate comma (map text vs)) $+$
>   text "enter clo" <+> text arg
> printExpr (VarM v) = text v 

> vcat' :: [Doc] -> Doc
> vcat' = foldl ($+$) empty

