> {-# LANGUAGE NoImplicitPrelude, FunctionalDependencies, 
>   MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
>   TypeSynonymInstances, GADTs #-}
>
> module Lambda1
>
> where
> 
> import Control.Monad.State (State(runState), get, put)
> import Text.PrettyPrint 
> import Prelude hiding (abs, flip, succ, id)
> import Data.List (union, delete)
> import Compiler.Hoopl
> import Control.Monad.State

> main = do
>   let hRuled title prog = do
>          putStrLn $ take 72 (repeat '-') 
>          putStrLn title
>          putStrLn $ take 72 (repeat '-') 
>          m2Prog prog
>   hRuled "compose" compose
>   hRuled "flip" flip
>   hRuled "id" id
>   hRuled "compose . id" composeId

``lambdaProg'' pretty-prints the original program:

> lambdaProg :: Prog -> IO ()
> lambdaProg = putStrLn . printL

``m2Prog'' compiles a lambda program to a monadic language:

> m2Prog :: Prog -> IO ()
> m2Prog = putStrLn . printM2 . compileM2

Some functions. A helper for defining abstractions first. The class declaration
lets me pass nested tuples for multiple arguments:

> abs :: (Names a, Args a b) => a -> (b -> Expr) -> Expr
> abs n body = Abs (names n) (body (vars n))

The compose function. The definition and the program must be 
separate so compose can be re-used later.:

> compose :: Prog 
> compose = [("compose", composeDef)]

> composeDef :: Expr           
> composeDef  = abs ("f",("g", "x")) $ 
>               \(f, (g, x)) -> App f (App g x)

Flip:

> flip :: Prog
> flip = [("flip", def)]
>   where
>     def = abs "f" $ \f ->
>           abs "a" $ \a ->
>           abs "b" $ \b ->
>           App (App f b) a

Identity:

> id :: Prog
> id = [("id", idDef)]

> idDef :: Expr
> idDef = abs "x" $ \x -> x

Identity w/ compose:

> composeId = [("composeId", (App composeDef (App composeDef idDef)))]

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

> type DefM2 = (Fun, [Captured], Arg, ExprM2 O C)

An program is a sequence of function definitions, which can be 
mutually recursive:\footnote{Not yet implemented}

> type ProgM2 = [DefM2]

A monadic expression consists of one of the four terms below. ``v''
indicates that the term cannot take an arbitrary expression, only a
variable. 

  expr ::= return v
    | enter v1 v2
    | closure v [v1, ..., vN]
    | v <- prog

Expressions in this language can be in tail position (at the
end of a do block) or not. Tail position expressions have type 
``ExprM2 e O'', where ``e'' can be either ``O'' or ``C'' (from Hoopl). 

> data ExprM2 e x where 

First I describe the tail position instructions. ReturnT just returns
the variable specified.

>   ReturnT :: Name -> ExprM2 O C

``ClosureT'' allocates a closure pointing to particular function, with
a list of captured variables.

>   ClosureT :: Fun -- The variable holding the address of the function.
>     -> [Captured] -- List of captured free varaibles
>     -> ExprM2 O C

Enter a closure in the first postion with an argument in the
second. ``EnterT'' always returns a value, making it a closed
instruction.

>   EnterT :: Name -- Variable holding the closure
>     -> Name  -- Argument to the function.
>     -> ExprM2 O C

Now the open instructions. ``BindT'' does not return a
value. However, the expression it evaluates must be closed. The code
following ``BindT'' can be open or closed, which gets reflected in 
``BindT's'' type. This might get us in trouble later when we use
Hoopl to combine multiple instructions together -- I think it will want
BindT to be Open-Open, but it works for now.

>   BindT :: Name  -- Name of variable to bidn value to.
>     -> ExprM2 e1 C   -- Expression that computes the value we want.
>     -> ExprM2 O x1   -- Code following the bind.
>     -> ExprM2 O x1   

LetT introduces local function definitions. Each definition a list of
captured variables and argument. The body of the function must be
closed, though it can consist of multiple expressions. LetT gets the
same type as BindT, with the same caveats.

>   LetT :: Name 
>     -> [Captured]  -- Captured variables expected in the closure.
>     -> Arg         -- Name of arg to function
>     -> ExprM2 e1 C -- Body of function definition
>     -> ExprM2 O x1 -- Code following the Let
>     -> ExprM2 O x1 

To compile an expression, ``compExprM2'' gets a function that will
``finish'' the compilation (i.e., ``fin''). Each case passes the
instruction that should go at the end of the compiled expression, for
that particular expression. Hoopl's ``C'' type guarantees that only a
tail-position instruction can end a expression. ``fin'' always returns
free variables as well, so that the compilation can determine which
arguments will need to be captured in closures, or will appear as
top-level arguments.

> compExprM2 :: Expr 
>            -> ([Name] 
>                -> ExprM2 O C 
>                -> CompM2 ([Name], ExprM2 O C)) 
>            -> CompM2 ([Name], ExprM2 O C)

A variable merely returns its value. The variable is the only free
varialbe, as well, so it gets passed along.

> compExprM2 (VarL v) fin = fin [v] (ReturnT v)

For application, we must ensure that the values of e1 and e2 get into
variables. Once variables are bound, an ``EnterT'' instruction will
implement the application. The ``fin'' function given is used once
we have e1 and e2 in variables. Free variables won't be changed so
we just pass the union of free variables found during compilation of e1
and e2.

> compExprM2 (App e1 e2) fin = 
>   compVar e1 $ \e1fvs f ->
>   compVar e2 $ \e2fvs x ->
>     fin (union e1fvs e2fvs) (EnterT f x)

> compExprM2 (Abs vs e) fin = do
>   let compClosure [] = compExprM2 e (\lvs b -> return (lvs, b))
>       compClosure (a:as) = do
>         (cvs, b) <- compClosure as
>         let cvs' = delete a cvs
>         f <- fresh "q"
>         return (cvs', (LetT f cvs' a b (ClosureT f cvs')))
>   dummy <- fresh "dummy"
>   (cvs, b) <- if null vs
>               then compClosure [dummy]
>               else compClosure vs
>   fin cvs b

> compVar :: Expr 
>         -> ([Name] -> Name -> CompM2 ([Name], ExprM2 O C))
>         -> CompM2 ([Name], ExprM2 O C)
> compVar (VarL v) finV = finV [v] v
> compVar e finV = compExprM2 e $ \efvs t -> do
>   a <- fresh "a"
>   (efvs', rest) <- finV efvs a 
>   return (efvs', BindT a t rest)

> type CompM2 = State Int

> compDefM2 :: Def -> CompM2 DefM2
> compDefM2 (f, body) = do
>   (fvs, body) <- compExprM2 body (\fvs t -> return (fvs, t))
>   dummy <- fresh "dummy"
>   (capts, arg) <- getCaptures fvs
>   return (f, capts, arg, body)                   

> getCaptures :: [Name] -> CompM2 ([Name], Name)
> getCaptures [] = do
>   dummy <- fresh "dummy"
>   return ([], dummy)
> getCaptures vs = return (init vs, last vs)

> compileM2 :: Prog -> ProgM2
> compileM2 = compile compDefM2 0

> printM2 :: ProgM2 -> String
> printM2 = render . vcat' . map printDefM2 

> printDefM2 :: DefM2 -> Doc
> printDefM2 (f, capts, arg, body) = decl <+> text "do" $+$ nest 2 (printExprM2s body)
>   where
>     decl = text f <+> braces (commaSep text capts) <+> text arg <+> text "="
>     amt = 1

> printExprM2s :: ExprM2 e x -> Doc
> printExprM2s (ReturnT n) = text "return" <+> text n
> printExprM2s (ClosureT f vs) = text "closure" <+> text f <+> braces (commaSep text vs)
> printExprM2s (EnterT f a) = text f <+> text "@" <+> text a
> printExprM2s (BindT n b r) = text n <+> text "<- do" <+> nest 2 (printExprM2s b) $+$ printExprM2s r
> printExprM2s (LetT f capts arg b r) = text "let" <+> text f <+> 
>                                       braces (commaSep text capts) <+> text arg <+> text "=" <+>
>                                       text "do" $$ nest 2 (printExprM2s b) $+$
>                                       printExprM2s r

> fresh :: (MonadState Int m) => String -> m String
> fresh prefix = do
>   i <- get
>   put (i + 1)
>   return (prefix ++ show i)

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

> commaSep = punctuated comma 
> spaced = punctuated space 

> punctuated :: Doc -> (a -> Doc) -> [a] -> Doc
> punctuated sep f = hcat . punctuate sep . map f

> vcat' :: [Doc] -> Doc
> vcat' = foldl ($+$) empty

Combinator for compiling our programs to different languages:

> compile compiler init prog = fst $ runState (mapM compiler prog) init

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

