> {-# LANGUAGE NoImplicitPrelude, FunctionalDependencies, 
>   MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
>   TypeSynonymInstances, GADTs #-}
>
> module Lambda1
>
> where
> 
> import Control.Monad.State (MonadState, State(runState)
>                             , get, put, modify)
> import Control.Exception (bracket_)
> import Text.PrettyPrint 
> import Prelude hiding (abs, flip, succ, id)
> import Data.List (union, delete)
> import Compiler.Hoopl ((|*><*|), (<*>), mkFirst, mkLast, mkMiddle
>                       , O, C, emptyClosedGraph, Graph, Graph'(..)
>                       , NonLocal(..), Label, freshLabel, IsMap(..)
>                       , Block, MaybeO(..), MaybeC(..), blockToNodeList
>                       , Unique, UniqueMonad(freshUnique), intToUnique)

> main = do
>   let hRuled prog = do
>          let sep = putStrLn $ take 72 (repeat '-') 
>          bracket_ sep sep (mProg prog)  
>   hRuled compose
>   hRuled flip
>   hRuled id
>   hRuled composeId

``lambdaProg'' pretty-prints the original program:

> lambdaProg :: Prog -> IO ()
> lambdaProg = putStrLn . printL

``mProg'' compiles a lambda program to a monadic language:

> mProg :: Prog -> IO ()
> mProg = putStrLn . printM . compileM

Some functions. A helper for defining abstractions first. 

> abs :: String -> (Expr -> Expr) -> Expr
> abs n body = Abs n (body (VarL n))

The compose function. The definition and the program must be 
separate so compose can be re-used later.:

> compose :: Prog 
> compose = [("compose", composeDef)]

> composeDef :: Expr           
> composeDef  = abs "f" $ \f -> 
>               abs "g" $ \g -> 
>               abs "x" $ \x -> App f (App g x)

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
> type Env = [Name]
> type Prog = [Def]
> type Captured = String
> type Arg = String

Define \lamA terms:

> type Def = (Name, Expr)

> data Expr = App Expr Expr
>   | Abs Name Expr
>   | VarL Name
>   deriving (Eq, Show)

Our monadic language. A monadic expression consists of one of the four
terms below. ``v'' indicates that the term cannot take an arbitrary
expression, only a variable.

  expr ::= return v
    | enter v1 v2
    | closure v [v1, ..., vN]
    | v <- prog

Expressions in this language can be in tail position (at the
end of a do block) or not. Tail position expressions have type 
``ExprM e O'', where ``e'' can be either ``O'' or ``C'' (from Hoopl). 

> data ExprM e x where 

First I describe the tail position instructions. ReturnT just returns
the variable specified.

>   Return :: Name -> ExprM O C

``Closure'' allocates a closure pointing to particular function, with
a list of captured variables.

>   Closure :: Name -- The variable holding the address of the function.
>     -> [Captured] -- List of captured free varaibles
>     -> ExprM O C

Enter a closure in the first postion with an argument in the
second. ``Enter'' always returns a value, making it a closed
instruction.

>   Enter :: Name -- Variable holding the closure
>     -> Name  -- Argument to the function.
>     -> ExprM O C

Now the open instructions. ``Bind'' does not return a
value. However, the expression it evaluates must be closed. The code
following ``Bind'' can be open or closed, which gets reflected in 
``Bind's'' type. This might get us in trouble later when we use
Hoopl to combine multiple instructions together -- I think it will want
Bind to be Open-Open, but it works for now.

>   Bind :: Name  -- Name of variable that will be bound.
>     -> ExprM O C   -- Expression that computes the value we want.
>     -> ExprM O O   -- Open/open since bind does not end an expression

>   Fun :: Label       -- Label for the function's entry point.
>     -> Name       -- Name of the function
>     -> [Captured] -- List of variables expected in closure
>     -> Maybe Arg  -- Name of argument
>     -> ExprM C O  -- One entry and exit makes functions closed/closed

To compile an expression, ``compExprM'' gets a function that will
``finish'' the compilation (i.e., ``fin''). Each case passes the
instruction that should go at the end of the compiled expression, for
that particular expression. Hoopl's ``C'' type guarantees that only a
tail-position instruction can end a expression. ``fin'' always returns
free variables as well, so that the compilation can determine which
arguments will need to be captured in closures, or will appear as
top-level arguments.

> instance NonLocal ExprM where
>   entryLabel (Fun l _ _ _) = l
>   successors _ = []

> compExprM :: Expr 
>            -> ([Name] 
>                -> ExprM O C 
>                -> CompM ([Name], Graph ExprM O C)) 
>            -> CompM ([Name], Graph ExprM O C)

A variable merely returns its value. The variable is the only free
varialbe, as well, so it gets passed along.

> compExprM (VarL v) fin = fin [v] (Return v)

For application, we must ensure that the values of e1 and e2 get into
variables. Once variables are bound, an ``Enter'' instruction will
implement the application. The ``fin'' function given is used once
we have e1 and e2 in variables. Free variables won't be changed so
we just pass the union of free variables found during compilation of e1
and e2.

> compExprM (App e1 e2) fin = 
>   compVar e1 $ \e1fvs f ->
>   compVar e2 $ \e2fvs x ->
>     fin (union e1fvs e2fvs) (Enter f x)

> compExprM (Abs v e) fin = do
>   let compClosure a = do
>         (cvs, b) <- compExprM e (\lvs b -> return (lvs, mkLast b)) 
>         let cvs' = delete a cvs
>         f <- fresh "q"
>         newFun f cvs' (Just a) b 
>         return (cvs', Closure f cvs')
>   (cvs, b) <- compClosure v
>   fin cvs b

> compVar :: Expr 
>         -> ([Name] -> Name -> CompM ([Name], Graph ExprM O C))
>         -> CompM ([Name], Graph ExprM O C)
> compVar (VarL v) finV = finV [v] v
> compVar e finV = compExprM e $ \efvs t -> do
>   a <- fresh "a"
>   (efvs', rest) <- finV efvs a 
>   return (efvs', mkMiddle (Bind a t) <*> rest)

> newFun :: Name 
>         -> [Captured] 
>         -> Maybe Arg 
>         -> Graph ExprM O C
>         -> CompM (Graph ExprM C C)
> newFun f capt arg body = do
>   l <- freshLabel
>   let def = mkFirst (Fun l f capt arg) <*> body
>   (i, defs) <- get
>   put (i, def |*><*| defs)
>   return def

Our compiler monad can create fresh variables and store multiple
function definitions:

> type CompM = State (Int, Graph ExprM C C)

> instance UniqueMonad CompM where
>   freshUnique = freshVal

> compFunM :: Def -> CompM (Graph ExprM C C)
> compFunM (f, body) = do
>   (fvs, bodyM) <- compExprM body (\fvs t -> return (fvs, mkLast t))
>   (capts, arg) <- getCaptures fvs
>   newFun f capts arg bodyM

> getCaptures :: [Name] -> CompM ([Name], Maybe Name)
> getCaptures [] = do
>   return ([], Nothing)
> getCaptures vs = return (init vs, Just (last vs))

> compileM :: Prog -> Graph ExprM C C
> compileM = snd . foldl compDef (0, emptyClosedGraph)
>   where
>     compDef s p = snd . runState (compFunM p) $ s

> printM :: Graph ExprM C C -> String
> printM = render . vcat' . printGraph
>   where
>     printGraph :: Graph ExprM x e -> [Doc]
>     printGraph GNil = []
>     printGraph (GUnit block) = [printBlock block]
>     printGraph (GMany entry middles exit) = printBlockMaybe entry :
>                                             (map printBlock . mapElems $ middles) ++
>                                             [printBlockMaybe exit]
>     printBlock :: Block ExprM x e -> Doc
>     printBlock = p . blockToNodeList
>       where p (e, bs, x) = hang (printNodeMaybe e) 2
>                                 (vcat' (map printExprMs bs) $+$
>                                        printNodeMaybe x)
>     printBlockMaybe :: MaybeO e1 (Block ExprM e2 x) -> Doc
>     printBlockMaybe (JustO b) = printBlock b
>     printBlockMaybe _ = empty
>     printNodeMaybe :: MaybeC e1 (ExprM e2 x) -> Doc
>     printNodeMaybe (JustC e) = printExprMs e

> printExprMs :: ExprM e x -> Doc
> printExprMs (Return n) = text "return" <+> text n
> printExprMs (Closure f vs) = text "closure" <+> text f <+> braces (commaSep text vs)
> printExprMs (Enter f a) = text f <+> text "@" <+> text a
> printExprMs (Bind n b) = text n <+> text "<- do" <+> nest 2 (printExprMs b)
> printExprMs (Fun _ f capts arg) = decl <+> text "do" 
>   where
>     decl = text f <+> braces (commaSep text capts) <+> parens (maybe empty (text) arg) <+> text "="
>     amt = 1

> fresh :: String -> CompM String
> fresh prefix = do
>   (i, p) <- get
>   put (i + 1, p)
>   return (prefix ++ show i)

> freshVal :: CompM Unique
> freshVal = do
>   (i, p) <- get
>   put (i + 1, p)
>   return (intToUnique i)

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
> printExprL n (Abs v e1) = text "\\" <> text v <> text "." <+> printExprL (n + 2) e1
> printExprL n (VarL v) = text v

> commaSep = punctuated comma 
> spaced = punctuated space 

> punctuated :: Doc -> (a -> Doc) -> [a] -> Doc
> punctuated sep f = hcat . punctuate sep . map f

> vcat' :: [Doc] -> Doc
> vcat' = foldl ($+$) empty

