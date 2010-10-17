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

> abs :: Name -> (Expr -> Expr) -> Expr
> abs n body = Abs [n] (body (VarL n))

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

> type Name = String
> type Fun = String
> type Env = [Name]
> type Prog = [Def]

Define \lamA terms:

> type Def = (Fun, Expr)

> data Expr = App Expr Expr
>   | Abs [Name] Expr
>   | VarL Name
>   deriving (Eq, Show)

Our monadic language. Top-level definitions have a name, list of arguments
and a body:

> type DefM = (Fun, [Name], [ExprM])

An program is a sequence of monadic expressions: 

  prog ::= m1; ...; mN

or

> type ProgM = [DefM]


A monadic expression consists of one of the five terms below. ``v''
indicates that the term cannot take an arbitrary expression, only a
variable. 

  expr ::= return v
    | v <- prog
    | enter v1 v2
    | closure v [v1, ..., vN]
    | v
 
> data ExprM = Return Name
>   | Bind Name ExprM 
>   | Enter Name Name
>   | Closure Name [Name] 
>   | Let Name [Name] [ExprM]
>   | Var Name
>   deriving (Eq, Show)

Compilation scheme:
   
[[app e1 e2]] => do
   v1 <- [[e1]]
   v2 <- [[e2]]
   enter v1 v2

[[abs v1, v2, ..., vN e]] = do
  let f(v1, ..., vN ++ free(e)) = [[e]]
  closure f ([v1, v2, ..., vn] ++ free(e))

[[var v]] = return v

> compDef :: Def -> Comp DefM
> compDef (fun, body) = do
>   bodyM <- (compExpr [] body $ \_ p -> do
>              c <- fresh "c"
>              return [Bind c (Closure p []), Return c])
>   return (fun, [], bodyM)

Compiling expressions to our monadic language:

> compExpr :: Env -> Expr -> (Env -> Name -> Comp [ExprM]) -> Comp [ExprM]
> compExpr env (VarL v) k = k env v 
> compExpr env (App e1 e2) k = 
>   compExpr env e1 $ \env' v1 ->
>   compExpr env' e2 $ \env'' v2 -> do
>     r <- fresh "r"
>     rest <- k env'' r
>     return $ Bind r (Enter v1 v2) : rest

> compExpr env (Abs vs e1) k = do
>   f <- fresh "f"
>   (_, _, body) <- compDef (f, e1)
>   r <- fresh "r"
>   rest <- k env r
>   return $ Let f vs body
>            : Bind r (Closure f (vs ++ free env e1)) 
>            : rest

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

> free :: Env -> Expr -> [Name]
> free e ex = free' e ex
>   where
>     free' env (App e1 e2) = free' env e1 ++ free' env e2
>     free' env (Abs vs e1) = free' (vs ++ env) e1
>     free' env (VarL v) 
>           | v `elem` env = []
>           | otherwise = [v]
>                         
> compile :: Prog -> ProgM
> compile prog = fst $ runState (mapM compDef prog) 0


Utility functions for printing:

> printM :: ProgM -> String
> printM prog = render $ vcat' (map printDef prog)
>
> printDef :: DefM -> Doc
> printDef (name, vars, body) = decl <+> printExprs nesting body
>   where
>     decl = text name <> 
>            parens (commaSep text vars) <+> 
>            text "=" 
>     nesting = length (render decl) 

> printExprs :: Int -> [ExprM] -> Doc
> printExprs nesting exprs = text "do" $+$ nest (nesting * (-1)) (vcat' (map printExpr exprs))
> 
> printExpr :: ExprM -> Doc
> printExpr (Return n) = text "return" <+> text n
> printExpr (Bind n v) = text n <+> text "<-" <+> printExpr v
> printExpr (Enter f arg) = text "enter" <+> text f <+> text arg
> printExpr (Closure f vs) = text "closure" <+> text f <+> parens (commaSep text vs)
> printExpr (Let n vs body) = text "let" <+> printDef (n, vs, body)
> printExpr (Var v) = text v 


> commaSep :: (a -> Doc) -> [a] -> Doc
> commaSep f = hcat . punctuate comma . map f

> vcat' :: [Doc] -> Doc
> vcat' = foldl ($+$) empty

