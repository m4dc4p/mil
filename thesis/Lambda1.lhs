> {-# LANGUAGE NoImplicitPrelude, FunctionalDependencies, MultiParamTypeClasses, FlexibleInstances, TypeSynonymInstances #-}
> module Lambda1
>
> where
> 
> import Control.Monad.State (State(runState), get, put)
> import Text.PrettyPrint 
> import Prelude hiding (abs, flip, succ)

To compile a program, give it to the run function:

> monProg :: Prog -> IO ()
> monProg = putStrLn . printM . compile

> lambdaProg :: Prog -> IO ()
> lambdaProg = putStrLn . printL

Some functions. A helper for defining abstractions first. The class declaration
lets me pass nested tuples for multiple arguments:

> abs :: (Names a, Args a b) => a -> (b -> Expr) -> Expr
> abs n body = Abs (names n) (body (vars n))

Then our friends the Church numerals. Starting with zero:

> zero :: Expr
> zero = abs ("s", "z") $ \(VarL _, z) -> z

We can define successor:

> succ :: Expr -> Expr
> succ n = abs ("n", ("s", "z")) $ \(n, (s, z)) -> 
>          App s (App (App n s) z)

A program to calculate three:

> three :: Prog
> three = [("three", succ (succ (succ zero)))]

Some other classics:

then the compose function:

> compose :: Prog 
> compose = [("compose", def)]
>   where
>     def = abs ("f",("g", "x")) $ 
>           \(f, (g, x)) -> App f (App g x)

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
> type Captured = String
> type Arg = String

Define \lamA terms:

> type Def = (Fun, Expr)

> data Expr = App Expr Expr
>   | Abs [Name] Expr
>   | VarL Name
>   deriving (Eq, Show)

Our monadic language. Top-level definitions have a name, list of arguments
and a body:

> type DefM = (Fun, [Captured], [Arg], [ExprM])

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
>   | Closure Fun [Captured] 
>   | Let Name [Captured] [Arg] [ExprM]
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
>   bodyM <- compExpr [] body $ \_ p -> return [Return p]
>   return (fun, [], [], bodyM)

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
>   (_, _, _, body) <- compDef (f, e1)
>   r <- fresh "r"
>   rest <- k env r
>   return $ Let f (free (vs ++ env) e1) vs body
>            : Bind r (Closure f vs) 
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

> printL :: Prog -> String
> printL prog = render $ vcat' (map printDefL prog)

> printDefL :: Def -> Doc
> printDefL (fun, expr) = decl <+> printExprL (maximum [0, nesting - 2]) expr
>   where
>     decl = text fun <+> text "="
>     nesting = length (render decl)
>   
> printExprL :: Int -> Expr -> Doc
> printExprL n (App e1 e2) = parens $ hang (printExprL n e1) n (printExprL n e2)
> printExprL n (Abs vs e1) = text "\\" <> spaced text vs <> text "." <+> printExprL (n + 2) e1
> printExprL n (VarL v) = text v

> printM :: ProgM -> String
> printM prog = render $ vcat' (map printDef prog)
>
> printDef :: DefM -> Doc
> printDef (name, capt, vars, body) = decl <+> printExprs nesting body
>   where
>     decl = text name <>
>            braces (commaSep text capt) <+>
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
> printExpr (Let n capt vs body) = text "let" <+> printDef (n, capt, vs, body)
> printExpr (Var v) = text v 


> commaSep = punctuated comma 
> spaced = punctuated space 

> punctuated :: Doc -> (a -> Doc) -> [a] -> Doc
> punctuated sep f = hcat . punctuate sep . map f

> vcat' :: [Doc] -> Doc
> vcat' = foldl ($+$) empty

Simple type-level lists to make definining abstractions easier:

> class Names a where
>   names :: a -> [Arg]
> instance Names String where
>   names a = [a] 
> instance (Names b) => Names (String, b) where
>   names (a, b) = a : names b

> class Args a b where
>   vars :: a -> b
> instance Args String Expr where
>   vars a = VarL a
> instance (Args a b) => Args (String, a) (Expr, b) where
>   vars (a, b) = (VarL a, vars b)

