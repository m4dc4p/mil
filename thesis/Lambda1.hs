 {-# LANGUAGE TypeSynonymInstances, GADTs #-}

module Lambda1

where

import Prelude hiding (abs, flip,id)
import Control.Monad.State (State, execState, modify, gets)
import Data.List (union, delete, intersperse)
import Text.PrettyPrint 
import Compiler.Hoopl ((|*><*|), (<*>), mkFirst, mkLast, mkMiddle
                      , O, C, emptyClosedGraph, Graph, Graph'(..)
                      , NonLocal(..), Label, freshLabel, IsMap(mapElems)
                      , Block, MaybeO(..), MaybeC(..), blockToNodeList'
                      , Unique, UniqueMonad(freshUnique), intToUnique)

main = 
  mapM_ putStrLn .
  intersperse (replicate 72 '=') . 
  map (render . printProg) $ [compose, flip, id, composeId]

-- ``mProg'' compiles a lambda program to a monadic language:

printProg :: Prog -> Doc
printProg p = hang (printL p <+> text "==>") 2 (printM . compileM $ p)

-- Some functions. A helper for defining abstractions first. 

abs :: String -> (Expr -> Expr) -> Expr
abs n body = Abs n (body (VarL n))

{-The compose function. The definition and the program must be 
separate so compose can be re-used later.: -}

compose :: Prog 
compose = [("compose", composeDef)]

composeDef :: Expr           
composeDef  = abs "f" $ \f -> 
              abs "g" $ \g -> 
              abs "x" $ \x -> App f (App g x)

-- Flip:

flip :: Prog
flip = [("flip", def)]
  where
    def = abs "f" $ \f ->
          abs "a" $ \a ->
          abs "b" $ \b ->
          App (App f b) a

-- Identity:

id :: Prog
id = [("id", idDef)]

idDef :: Expr
idDef = abs "x" $ \x -> x

-- Identity w/ compose:

composeId = [("composeId", (App composeDef (App composeDef idDef)))]

-- Now we define the language used above. Some useful synonyms first:

type Name = String
type Prog = [Def]

-- A definition in our lambda calculus pairs a name with an expression:

type Def = (Name, Expr)

{-An expression in our language can be an application, abstraction or variable
name: -}

data Expr = App Expr Expr
  | Abs Name Expr
  | VarL Name
  deriving (Eq, Show)

{-The monadic target language for our compiler. A monadic program
consists of a sequence of function definitions. Each function expects
zero or more variables in its closure (the ``captured'' variables) and
an optional argument. The body of the functions consists of zero or
more statements, ended by one tail statement.

  defM ::= funM {a1, ..., aN} a = bodyM

  bodyM ::= do 
    stmtM1; 
    ... ; 
    stmtMN; 
    tailM

The language's one statement:

  stmtM ::= v <- bodyM

Tail expressions always return a value. ``v'' indicates that the term
cannot take an arbitrary expression, only a variable. ``closure''
creates a closure value pointing at the function indicated by v1,
capturing the values of the variables v1 to vN. ``enter'' implements
function application, using a closure constructed by ``closure''.

  tailM ::= return v
    | enter v1 v2
    | closure v [v1, ..., vN]

The terms of the language can be expressed in the data type
below. ``e'' and ``x'' index the open or closed type of each
instruction. Notice that sequencing does not get stored in this
structure. For example, the Bind instruction does not specify the
statements that follow it. Hoopl's Block and Graph types express
sequencing as built by the compiler. -}

data ExprM e x where 
  Fun :: Label      -- Label for the function's entry point.
    -> Name         -- Name of the function
    -> [Name]       -- List of variables expected in closure
    -> Maybe Name   -- Name of argument
    -> ExprM C O    -- One entry and exit makes functions
                    -- closed/closed

  Bind :: Name      -- Name of variable that will be bound.
    -> ExprM O C    -- Expression that computes the value we want.
    -> ExprM O O    -- Open/open since bind does not end an expression

  Return :: Name 
    -> ExprM O C
  Enter :: Name     -- Variable holding the closure
    -> Name         -- Argument to the function.
    -> ExprM O C
  Closure :: Name   -- The variable holding the address of the
                    -- function.
    -> [Name]       -- List of captured free varaibles
    -> ExprM O C

{- 

The compiler returns a control flow graph (CFG) of expressions which
may be opened or closed on both exit and entry. We define the CFG
alias to represent that type. Many functions return a CFG coupled with a
list of free variables, which the CFGWithFree alias represents.

-}

type CFG = Graph ExprM

type CFGWithFree e x = ([Name], CFG e x)

{-
Our compiler monad can create fresh
variables and store multiple function definitions, making it a State
monad.

The UniqueMonad instance allows us to create Hoopl
labels. Without it we could not define entry points, so it gives us critical
functionality.

-}

type CompM = State (Int, CFG C C)

instance UniqueMonad CompM where
  freshUnique = freshVal

{- 

We cannot build blocks from ExprM nodes without the NonLocal (previously ``Edges'') instance, from Hoopl. It defines
how individual blocks in the control flow graph relate to each other. 

-}

instance NonLocal ExprM where
  entryLabel (Fun l _ _ _) = l
  successors _ = []

{- 

To compile an expression, ``compExprM'' gets a function that will
``finish'' the compilation (i.e., ``fin''). Each case passes the
instruction that should go at the end of the compiled expression, for
that particular expression. Hoopl's ``C'' type guarantees that only a
tail-position instruction can end a expression. ``fin'' always returns
free variables as well, so that the compilation can determine which
arguments will need to be captured in closures, or will appear as
top-level arguments.

-}

compExprM :: Expr 
           -> ([Name] 
               -> ExprM O C 
               -> CompM (CFGWithFree O C))
           -> CompM (CFGWithFree O C)

{- 

A variable merely returns its value. The variable is the only free
variable, as well, so it gets passed along.

-}

compExprM (VarL v) fin = fin [v] (Return v)

{-

For application, we must ensure that the values of e1 and e2 get into
variables. Once variables are bound, an ``Enter'' instruction will
implement the application. The ``fin'' function given is used once we
have e1 and e2 in variables. Free variables won't be changed so we
just pass the union of free variables found during compilation of e1
and e2.

-}

compExprM (App e1 e2) fin = 
  compVar e1 $ \e1fvs f ->
  compVar e2 $ \e2fvs x ->
    fin (union e1fvs e2fvs) (Enter f x)

compExprM (Abs v e) fin = do
  let compClosure a = do
        (cvs, b) <- compExprM e resultM
        let cvs' = delete a cvs
        f <- fresh "q"
        newFun f cvs' (Just a) b 
        return (cvs', Closure f cvs')
  (cvs, b) <- compClosure v
  fin cvs b

-- | Special-cased compiler which replaces blocks
-- which would just return a variable with the variable
-- itself.
compVar :: Expr 
        -> ([Name] -> Name -> CompM (CFGWithFree O C))
        -> CompM (CFGWithFree O C)
compVar (VarL v) finV = finV [v] v
compVar e finV = compExprM e $ \efvs t -> do
  a <- fresh "a"
  (efvs', rest) <- finV efvs a 
  return (efvs', mkMiddle (Bind a t) <*> rest)

-- | Create a new function defition. Adds the function
-- to the CFG for the whole program and returns
-- the function defined.
newFun :: Name 
        -> [Name] 
        -> Maybe Name
        -> CFG O C
        -> CompM (CFG C C)
newFun f capt arg body = do
  l <- freshLabel
  let def = mkFirst (Fun l f capt arg) <*> body
  modify (\(i, defs) -> (i, def |*><*| defs))
  return def

-- | Compile a lambda-calculus program to 
-- a monadic control-flow graph
compileM :: Prog -> CFG C C
compileM = snd . foldr compDef (0, emptyClosedGraph)
  where
    compDef p = execState (compFunM p) 
    splitFvs [] = ([], Nothing)
    splitFvs vs = (init vs, Just (last vs))
    compFunM :: Def -> State (Int, CFG C C) (CFG C C)
    compFunM (f, body) = do
      (fvs, bodyM) <- compExprM body resultM
      let (capts, arg) =  splitFvs fvs
      newFun f capts arg bodyM

-- | Create a fresh variable with the given
-- prefix.
fresh :: String -> CompM String
fresh prefix = do
  i <- gets fst
  modify (\(_, p) -> (i + 1, p))
  return (prefix ++ show i)

-- | Create a new unique value; used in the
-- instance declaration for (UniqueMonad CompM).
freshVal :: CompM Unique
freshVal = do
  i <- gets fst
  modify (\(_, p) -> (i + 1, p))
  return (intToUnique i)

-- | Makes the free vars and expression given
-- into the last node in a CFG.
resultM :: [Name] -> ExprM O C -> CompM (CFGWithFree O C)
resultM fvs t = return (fvs, mkLast t)

-- Functions for printing:

printM :: CFG C C -> Doc
printM = vcat' . printGraph
  where
    printGraph :: CFG x e -> [Doc]
    printGraph GNil = []
    printGraph (GUnit block) = [printBlock block]
    printGraph (GMany entry middles exit) = printBlockMaybe entry :
                                            (map printBlock . mapElems $ middles) ++
                                            [printBlockMaybe exit]
    printBlock :: Block ExprM x e -> Doc
    printBlock = p . blockToNodeList'
      where p (e, bs, x) = hang (printNodeMaybe e) 2
                                (vcat' (map printExprMs bs) $+$
                                       printNodeMaybe x)
    printBlockMaybe :: MaybeO e1 (Block ExprM e2 x) -> Doc
    printBlockMaybe (JustO b) = printBlock b
    printBlockMaybe _ = empty
    printNodeMaybe :: MaybeC e1 (ExprM e2 x) -> Doc
    printNodeMaybe (JustC e) = printExprMs e

printExprMs :: ExprM e x -> Doc
printExprMs (Return n) = text "return" <+> text n
printExprMs (Closure f vs) = text "closure" <+> text f <+> braces (commaSep text vs)
printExprMs (Enter f a) = text f <+> text "@" <+> text a
printExprMs (Bind n b) = text n <+> text "<- do" <+> nest 2 (printExprMs b)
printExprMs (Fun _ f capts arg) = decl <+> text "do" 
  where
    decl = text f <+> braces (commaSep text capts) <+> parens (maybe empty (text) arg) <+> text "="
    amt = 1

printL :: Prog -> Doc
printL prog = vcat' (map printDefL prog)

printDefL :: Def -> Doc
printDefL (fun, expr) = decl <+> printExprL (maximum [0, nesting - 2]) expr
  where
    decl = text fun <+> text "="
    nesting = length (render decl)
  
printExprL :: Int -> Expr -> Doc
printExprL n (App e1 e2) = parens $ hang (printExprL n e1) n (printExprL n e2)
printExprL n (Abs v e1) = text "\\" <> text v <> text "." <+> printExprL (n + 2) e1
printExprL n (VarL v) = text v

commaSep = punctuated comma 
spaced = punctuated space 

punctuated :: Doc -> (a -> Doc) -> [a] -> Doc
punctuated sep f = hcat . punctuate sep . map f

vcat' :: [Doc] -> Doc
vcat' = foldl ($+$) empty

