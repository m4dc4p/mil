> {-# LANGUAGE NoImplicitPrelude, FunctionalDependencies, 
>   MultiParamTypeClasses, FlexibleInstances, 
>   TypeSynonymInstances #-}
>
> module Lambda1
>
> where
> 
> import Control.Monad.State (State(runState), get, put)
> import Text.PrettyPrint 
> import Prelude hiding (abs, flip, succ)

To compile a program, use ``monProg'':

> monProg :: Prog -> IO ()
> monProg = putStrLn . printM . compile

``lambdaProg'' pretty-prints the original program:

> lambdaProg :: Prog -> IO ()
> lambdaProg = putStrLn . printL

Some functions. A helper for defining abstractions first. The class declaration
lets me pass nested tuples for multiple arguments:

> abs :: (Names a, Args a b) => a -> (b -> Expr) -> Expr
> abs n body = Abs (names n) (body (vars n))

The compose function:

> compose :: Prog 
> compose = [("compose", def)]
>   where
>     def = abs ("f",("g", "x")) $ 
>           \(f, (g, x)) -> App f (App g x)

> compose2 :: Prog 
> compose2 = [("compose2", def)]
>   where
>     def = abs "f" $ \f -> 
>           abs "g" $ \g ->
>           abs "x" $ \x -> App f (App g x)

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

Our monadic language. Functions take a closure containing free variables and a
single argument. A list of expressions make up the body of the function:

> type DefM = (Fun, [Captured], Arg, [ExprM])

An program is a sequence of function definitions, which can be 
mutually recursive:\footnote{Not yet implemented}

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
>   | Let Name [Captured] Arg [ExprM]
>   | Var Name
>   deriving (Eq, Show)

``return'' simply returns the variable given. ``<-'' (``bind'')
evaluates the sequence of statements on the right-hand side and
assigns the result to ``v.'' ``prog'' can create side-effects, such as
memory allocation. ``enter'' expects v1 to contain a closure. The
function body pointed to by the closure will be executed, using ``v2''
as the argument. The value created by ``closure'' will point to the
function referred to in ``v'' and will capture the variables
given. The function will expect to receive these variables along with
an argument. The list of captured variables can be empty. Finally,
``v'' simply refers to a variable in scope.

Following mon3.hs (and Andrew Kennedy), I use a continuation-based
compilation scheme. First, we must compile top-level
definitions. ``compDef'' takes a \lamA expression ``Def'' and produces
a monadic program, ``DefM''. The free variables (less one) become the
variables the definition expects in the closure given to it, if
any. The remaining free variable becomes an argument to the
function. If the funciton does not contain any free variables, a dummy
argument gets created.

> compDef :: Def -> Comp DefM
> compDef (fun, body) = do
>   bodyM <- compExpr [] body $ \_ p -> return [Return p]
>   let freeV = freeM [] bodyM
>   (captured, arg) <- if null freeV 
>                      then (do { dummy <- fresh "dummy"; return ([], dummy) })
>                      else return (init freeV, last freeV)
>   return (fun, captured, arg, bodyM)

``compExpr'' compiles an expression in a particular environment,
``Env''. It produces a list of monadic statements,
``[ExprM]]''. ``compExpr'' also gets a continuation \emph{for the
compiler}, which represents compiling the ``rest'' of the program. The
continuation takes a new environment and a name. The name represents
the result of the preceding portion of the program. This arguments
lets the compiler send destinations ``forward'', so later compilation
can use newly boudn variables.

> compExpr :: Env -> Expr -> (Env -> Name -> Comp [ExprM]) -> Comp [ExprM]

Compiling ``VarL'' means simply passing the name of the variable along to
the rest of the compilation.

> compExpr env (VarL v) k = k env v 

To compile ``App'', we first recursively compile ``e1'' and ``e2''.
Notice that the functions we pass to ``compExpr'' take an environment
and a variable name (``v1'' and ``v2''). These arguments represent the
destination in which ``e1'' and ``e2'' will put their values. This
allows us to ``know'' that ``v1'' and ``v2'' are variables. In turn,
``compExpr'' creates a destination for the application's result
(``r'') and passes that to the rest of the compiler (``k env'
r''). ``Enter'' and ``Bind'' instructions execute the application and
store its result in the previously created location, respectively. The
code generated by the ``rest'' of the compiler gets appended to these
instructions and returned.

> compExpr env (App e1 e2) k = 
>   compExpr env e1 $ \env' v1 ->
>   compExpr env' e2 $ \env'' v2 -> do
>     r <- fresh "r"
>     rest <- k env'' r
>     return $ Bind r (Enter v1 v2) : rest

An abstraction gets compiled to two distinct pieces. A local function,
``f'', gets defined. That function expects all free variables in the
body (``e1'') and all the abstaction's arguments, less one, to be
``captured'' in a closure. The function also takes one argument, which
may be a dummy if the abstraction doesn't define any arguments.

A closure gets created which points to the new local function and 
captures all the variables expected. The location of the closure
gets passed to the ``rest'' of the compiler. The code returned
defines the local function ``f'', makes sure ``r'' gets 
bound to the closure, and follows with the ``rest'' of the
code returned by calling the continuation (``k'') given.

> compExpr env (Abs vs e1) k = do
>   let captured = free (arg : env) e1
>       arg = last vs
>   body <- compExpr env e1 (\_ r -> return [Return r])
>   f <- fresh "f"
>   r <- fresh "r"
>   rest <- k (r : f : env) r
>   return $ Let f captured arg body
>            : Bind r (Closure f captured)
>            : rest

To find free variables in the monadic program, we analyze
each statement in turn and return a list of free names:

> freeM :: Env -> [ExprM] -> [Name]
> freeM initEnv = fst . foldl findFree ([], initEnv) 
>   where
>     findFree :: ([Name], Env) -> ExprM -> ([Name], Env)
>     findFree (fv, env) (Return n) = (n `inEnv` env ++ fv, env)
>     findFree (fv, env) (Bind n e) = (freeM env [e] ++ fv, n : env)
>     findFree (fv, env) (Enter n1 n2) = (n1 `inEnv` env ++ n2 `inEnv` env, env)
>     findFree (fv, env) (Closure f capts) =
>       (f `inEnv` env ++ concatMap (`inEnv` env) capts ++ fv, env)
>     findFree (fv, env) (Let n capt arg body) = (freeM (n : arg : capt ++ env) body ++ fv, n : env)
>     findFree (fv, env) (Var n) = (n `inEnv` env ++ fv, env)
>     inEnv :: Name -> Env -> [Name]
>     inEnv n env 
>       | n `elem` env = []
>       | otherwise = [n]
      
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
> printDef (name, capt, var, body) = decl <+> printExprs nesting body
>   where
>     decl = text name <>
>            braces (commaSep text capt) <+>
>            parens (text var) <+> 
>            text "=" 
>     nesting = length (render decl) 

> printExprs :: Int -> [ExprM] -> Doc
> printExprs nesting exprs = text "do" $+$ nest (nesting * (-1)) (vcat' (map printExpr exprs))
> 
> printExpr :: ExprM -> Doc
> printExpr (Return n) = text "return" <+> text n
> printExpr (Bind n v) = text n <+> text "<-" <+> printExpr v
> printExpr (Enter f arg) = text "enter" <+> text f <+> text arg
> printExpr (Closure f capts) = text "closure" <+> text f <+> braces (commaSep text capts)
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

