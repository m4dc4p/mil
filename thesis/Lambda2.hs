{-# LANGUAGE TypeSynonymInstances, GADTs #-}
module Lambda2

where

import Prelude hiding (abs, not)
import Control.Monad.State (State, execState, modify, gets)
import Text.PrettyPrint 
import Data.List (intersperse, (\\), union, nub)
import Compiler.Hoopl ((|*><*|), (<*>), mkFirst, mkLast, mkMiddle
                      , O, C, emptyClosedGraph, Graph, Graph'(..)
                      , NonLocal(..), Label, freshLabel, IsMap(mapElems)
                      , Block, MaybeO(..), MaybeC(..), blockToNodeList'
                      , Unique, UniqueMonad(freshUnique), intToUnique)


main = putStrLn . render . printDefs $ [nil, not, notNil]

{-

The lambda-calculus with cases and algebraic data types. Expressions
in the language include:

  expr ::= \x . e  -- abstraction
       |   e1 e2   -- application
       |   v       -- variables
       |   case e1 of [alt1, ..., altN] -- Case discrimination
       |   C e1 ... eN -- Constructor 

  alt ::= C v1 ... vN -> e

A program consists of multiple, possibly recursive, top-level
definitions:

  def ::= f = expr

  prog ::= def1
           ...
           defN
-}

type Name = String
type Var = String
type Constructor = String

data Expr = Abs Var Expr
          | App Expr Expr
          | Var Var
          | Case Expr [Alt Expr]
          | Constr Constructor [Expr]
  deriving (Show, Eq)

type Env = [Name] 

data Alt e = Alt Constructor [Name] e
  deriving (Show, Eq)

type Def = (Name, Expr)
type Prog = [Def]

abs :: Var -> (Expr -> Expr) -> Expr
abs v f = Abs v (f (Var v))

false :: Expr
false = Constr "False" []

true :: Expr
true = Constr "True" []

nil :: Def 
nil = ("nil", nilDef)
  where
    nilDef = abs "xs" $ \xs -> Case xs [Alt "Nil" [] true
                                       , Alt "Cons" ["a", "b"] false]
not :: Def
not = ("not", notDef)
  where
    notDef = abs "f" $ \f -> Case f [Alt "True" [] false
                                    , Alt "False" [] true]

notNil :: Def
notNil = ("notNil", notNilDef)
  where
    notNilDef = abs "xs" $ \xs -> App (Var "not") (App (Var "nil") xs)

{-

Our monadic language:

  
  bodyM ::= do 
    stmtM1; 
    ... ; 
    stmtMN; 
    tailM

  stmtM ::= v <- bodyM

  tailM ::= return v
    | enter v1 v2         -- Call an unknown function.
    | call f(v1, ..., v)  -- Call a known function.
    | closure v [v1, ..., vN]
    | case v of [alt1, ..., altN]

  alt ::= C v1 ... vN -> bodyM

  defM ::= funM {v1, ..., vN} v = bodyM

  progM :: def1
           ...
           defN
-}

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
  CaseM :: Name     -- Variable to inspect
    -> [Alt (CFG O C)] -- Case arms
    -> ExprM O C
  ConstrM :: Constructor  -- Constructor name
    -> [Name]            -- Only variables allowes as arguments to
                         -- constructor.
    -> ExprM O C  

type CFG = Graph ExprM
type CFGEnv e x = (Env, CFG e x)
type CompM = State (Int, CFG C C)

compileExprM :: Env 
             -> Expr 
             -> (Env -> ExprM O C -> CompM (CFG O C)) 
             -> CompM (CFG O C)

compileExprM env (Var v) fin = fin env (Return v)

compileExprM env (App e1 e2) fin = 
  compVarM env e1 $ \_ f ->
  compVarM env e2 $ \_ x -> 
    fin env (Enter f x)

compileExprM env (Abs v e) fin = do
  let env' = v : env
      fvs = free env' e
      free = undefined
  clos <- do
    body <- compileExprM env' e (\_ t -> return (mkLast t))
    name <- fresh "c"
    addDefn name fvs (Just v) body
    return (Closure name fvs)
  fin env' clos

compileExprM env (Case expr alts) fin = 
  compVarM env expr $ \env' t -> do
    altsM <- mapM (compAlt env) alts
    fin (union env' env) (CaseM t altsM)
  where
    compAlt :: Env -> Alt Expr -> CompM (Alt (CFG O C))
    compAlt env (Alt cons vs e) = do
      expr <- compVarM (env \\ vs) e $ \_ t -> return (mkLast $ Return t)
      return (Alt cons vs expr)

compileExprM env (Constr cons es) fin = compileVarsM env es []
  where
    compileVarsM env (e:es) vs = compVarM env e $ \env' v ->
                                 compileVarsM env' es (v:vs) 
    compileVarsM env [] vs = fin env (ConstrM cons (reverse vs))
        
compVarM :: Env 
         -> Expr 
         -> (Env -> Name -> CompM (CFG O C)) 
         -> CompM (CFG O C)
compVarM env (Var v) fin = fin env v
compVarM env expr fin = compileExprM env expr $ \env' t -> do
  a <- fresh "a"
  rest <- fin env' a
  return $ mkMiddle (Bind a t) <*> rest
  

compileM :: Prog -> CFG C C
compileM defs = snd . foldr compDef (0, emptyClosedGraph) $ defs
  where
    top = nub (map fst defs) -- top level definitions
    compDef p = execState (compFunM p)
    compFunM :: Def -> CompM (CFG C C)
    compFunM (f, body) = do
      bodyM <- compileExprM top body undefined
      addDefn f [] Nothing bodyM

addDefn :: Name -> [Name] -> Maybe Name -> CFG O C -> CompM (CFG C C)
addDefn = undefined

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

instance UniqueMonad CompM where
  freshUnique = freshVal

instance NonLocal ExprM where
  entryLabel (Fun l _ _ _) = l
  successors _ = []

-- Printing lambda-calculus terms

printDefs :: [Def] -> Doc
printDefs ds = vcat' 
               . intersperse (text (replicate 72 '=')) 
               . map printDef $ ds

printDef :: Def -> Doc
printDef (name, body) = hang (text name <+> text "=") 2 (printExpr body) 

printExpr :: Expr -> Doc
printExpr (Abs var e) = text "\\" <> text var <> text "." <+> printExpr e
printExpr (App e1 e2) = printVar e1 <+> printVar e2
printExpr (Var v) = text v
printExpr (Case e alts) = hang (text "case" <+> printExpr e <+> text "of") 2 (vcat' . map printAlt $ alts)
  where
    printAlt (Alt cons vs e) = text cons <+> (hsep . map text $ vs) <+> text "->" <+> printExpr e
printExpr (Constr cons exprs) = text cons <+> (hsep . map printVar $ exprs)

printVar (Var v) = text v
printVar e = parens (printExpr e)

vcat' :: [Doc] -> Doc
vcat' = foldl ($+$) empty
