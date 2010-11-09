{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns #-}

module Lambda2

where

import Prelude hiding (abs)
import Control.Monad.State (State, execState, modify, gets)
import Text.PrettyPrint 
import Data.List (intersperse, (\\), union, nub, delete)
import Compiler.Hoopl ((|*><*|), (<*>), mkFirst, mkLast, mkMiddle
                      , O, C, emptyClosedGraph, Graph, Graph'(..)
                      , NonLocal(..), Label, freshLabel, IsMap(mapElems)
                      , Block, MaybeO(..), MaybeC(..), blockToNodeList'
                      , Unique, UniqueMonad(freshUnique), intToUnique)


{-

The lambda-calculus with cases and algebraic data types. Expressions
in the language include:

  expr ::= \x {fvs}. e  -- abstraction w/ free variables annotated
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

data Expr = Abs Var Env Expr
          | App Expr Expr
          | Var Var
          | Case Expr [Alt Expr]
          | Constr Constructor [Expr]
  deriving (Show, Eq)

data Alt e = Alt Constructor [Name] e
  deriving (Show, Eq)

type Env = [Name] 
type Def = (Name, Expr)
type Prog = [Def]

{-

Our monadic language:

  
  bodyM ::= do 
    stmtM1; 
    ... ; 
    stmtMN; 
    tailM

  stmtM ::= v <- tailM
    | case v of [alt1, ..., altN]
    | tailM

  tailM ::= return v
    | v1 @ v2         -- Call an unknown function.
    | f(v1, ..., v)  -- Call a known function.
    | closure f {v1, ..., vN} -- Create closure pointing to a function.

  alt ::= C v1 ... vN -> call f(v1, ..., vN)

  defM ::= f {v1, ..., vN} v = bodyM -- ``f'' stands for the name of the function.

  progM :: defM1
           ...
           defMN
-}

data StmtM e x where
  -- | Entry point to a list of statements.
  Entry :: Name -- Name of the function
    -> [Name]   -- Arguments
    -> Label    -- Label of the entry point.
    -> StmtM C O

  Bind :: Name      -- Name of variable that will be bound.
    -> TailM    -- Expression that computes the value we want.
    -> StmtM O O    -- Open/open since bind does not end an expression
  
  CaseM :: Name      -- Variable to inspect
      -> [Alt TailM] -- Case arms
      -> StmtM O C
      
  Done :: TailM  -- Finish a block.
      -> StmtM O C

-- | TailM conclueds a list of statements. Each
-- block ends with a TailM except when CaseM ends
-- the blocks.
data TailM = Return Name 
  | Enter Name     -- Variable holding the closure
      Name         -- Argument to the function.
  | Closure Name   -- The variable holding the address of the function.
      [Name]       -- List of captured free varaibles
  | Call Name     -- Name of function
      [Name]       -- Arguments to functino
  | ConstrM Constructor  -- Constructor name
      [Name]            -- Only variables allowes as arguments to constructor.
  deriving (Eq, Show)

-- Compiling from lambda-calculus to the monadic language.

compileM :: Prog -> ProgM C C
compileM defs = compG $ foldr compDef initial $ addFVs defs
  where
    compDef p = execState (uncurry newDefn p)
    initial = C 0 emptyClosedGraph []
    -- | Creates a new function definition
    -- using the arguments given and adds it
    -- to the control flow graph.    
    newDefn :: Name -> Expr -> CompM ()
    newDefn name body = do
      addTop name
      prog <- compileStmtM body (return . mkLast . Done)
      addDefn name (collectFree body) prog
    -- | Collect free variables from Abs terms on 
    -- the lambda-calculus expression.
    collectFree :: Expr -> [Name]
    collectFree (Abs _ vs _) = vs
    collectFree (App e1 e2) = collectFree e1 ++ collectFree e2
    collectFree (Var v) = [] 
    collectFree (Case e alts) = collectFree e ++ concatMap (\(Alt _ _ e) -> collectFree e) alts
    collectFree (Constr _ exprs) = concatMap collectFree exprs

compileStmtM :: Expr 
  -> (TailM -> CompM (ProgM O C))
  -> CompM (ProgM O C)

compileStmtM (Var v) ctx 
  = ctx (Return v)

compileStmtM (App e1 e2) ctx 
  = compVarM e1 $ \f ->
    compVarM e2 $ \g ->
      ctx (Enter f g)

compileStmtM (Case e alts) ctx = do
  r <- fresh "result"
  f <- ctx (Return r) >>= callDefn "caseJoin" 
  let compAlt (Alt cons vs body) = do
        body' <- compileStmtM body (\t -> return (mkMiddle (Bind r t) <*> mkLast (Done f))) >>= callDefn ("altBody" ++ cons)
        return (Alt cons vs body')
  altsM <- mapM compAlt alts
  compVarM e $ \v -> return (mkLast (CaseM v altsM))
  where
  callDefn :: String 
           -> ProgM O C 
           -> CompM TailM
  callDefn name body = do 
    f <- newTop name 
    tops <- gets compT
    -- Collect free variables in a program.
    let freeM :: ProgM O C -> [Name] 
        freeM = filter (not . null) . concat . maybeGraph [[]] freeB

        freeB :: Block StmtM x e -> [Name] 
        freeB b = 
          let (e, bs, x) = blockToNodeList' b
              mids = foldr useDef (maybeC id useDef x [])  bs

              useDef                    :: StmtM e x -> [Name] -> [Name] 
              useDef (Entry _ _ _) live = live
              useDef (Bind v t) live    = delete v live ++ useTail t
              useDef (CaseM v alts) _   = v : concatMap (\(Alt _ vs t) -> useTail t \\ vs) alts
              useDef (Done t) live      = live ++ useTail t

              useTail                :: TailM -> [Name] 
              useTail (Return v)     = [v]
              useTail (Enter v1 v2)  = [v1, v2]
              useTail (Closure v vs) = v : vs
              useTail (Call v vs)    = v : vs
              useTail (ConstrM _ vs) = vs

          in maybeC id useDef e mids
        fvs = nub (freeM body \\ tops)
    addDefn f fvs body
    return (Call f fvs)

compileStmtM (Abs v fvs b) ctx = do
  let makeFunction b fvs = do
        prog <- compileStmtM b (return . mkLast . Done)
        name <- newTop "absBody"
        addDefn name (v:fvs) prog
        return name
  f <- makeFunction b fvs
  ctx (Closure f fvs)

compileStmtM (Constr cons exprs) ctx = 
  let compExpr vs [] = ctx (ConstrM cons (reverse vs))
      compExpr vs (e:es) = compVarM e $ \v -> 
                           compExpr (v:vs) es
  in compExpr [] exprs


compVarM :: Expr 
  -> (Name -> CompM (ProgM O C))
  -> CompM (ProgM O C)
compVarM (Var v) ctx = ctx v
compVarM e ctx       = compileStmtM e $ \t -> do
  v <- fresh "v"
  rest <- ctx v
  return (mkMiddle (v `Bind` t) <*> rest)

-- Compiler State

-- | Compiler state. 
data CompS = C { compI :: Int -- ^ counter for fresh variables
               , compG :: (ProgM C C) -- ^ Program control-flow graph.
               , compT :: [Name] } -- ^ top-level function names.
               
type ProgM = Graph StmtM
type CompM = State CompS

-- | Add a name to the list of top-level functions.
addTop :: Name -> CompM ()
addTop name = modify (\s@(C { compT }) -> s { compT = name : compT })

-- | Make a new top-level function name, based on the
-- prefix given.
newTop :: Name -> CompM Name
newTop name = do
  f <- fresh name
  addTop f
  return f

-- | Adds a function definition to the
-- control flow graph.
addDefn :: Name -> [Name] -> ProgM O C -> CompM ()
addDefn name args progM = do
  l <- freshLabel
  let def = mkFirst (Entry name args l) <*> progM
  modify (\s@(C { compG, compT }) -> s { compG = def |*><*| compG })

-- | Create a fresh variable with the given
-- prefix.
fresh :: String -> CompM String
fresh prefix = do
  i <- gets compI
  modify (\s@(C { compI }) -> s { compI = compI + 1})
  return (prefix ++ show i)

-- | Create a new unique value; used in the
-- instance declaration for (UniqueMonad CompM).
freshVal :: CompM Unique
freshVal = do
  i <- gets compI
  modify (\s@(C { compI }) -> s { compI = compI + 1})
  return (intToUnique i)

instance UniqueMonad CompM where
  freshUnique = freshVal

instance NonLocal StmtM where
  entryLabel (Entry _ _ l) = l
  successors _ = []

-- | Annotate lambda-calculus programs with free variables.
addFVs :: Prog -> Prog
addFVs ps = map (\(name, body) -> (name, snd $ annotate body)) ps
  where
    -- top level definitions
    top = map fst ps
    -- Add free variables to each lambda.
    annotate :: Expr -> (Env, Expr)
    annotate (Abs v _ expr)   
      = let (fvs, expr') = annotate expr
            fvs'         = nub (delete v fvs)
        in (fvs', Abs v fvs' expr')
    annotate (App e1 e2)      
      = let (fvs1, e1') = annotate e1
            (fvs2, e2') = annotate e2
        in (fvs1 ++ fvs2, App e1' e2')
    annotate e@(Var v)  
      | v `elem` top = ([], e)
      | otherwise = ([v], e)
    annotate (Case e alts)    
      = let (fvs1, e')    = annotate e
            (fvs2, alts') = unzip $ map annotateAlt alts
        in (fvs1 ++ concat fvs2, Case e' alts')
    annotate (Constr c exprs) 
      = let (fvs1, exprs') = unzip $ map annotate exprs
        in (concat fvs1, Constr c exprs')
    annotateAlt (Alt c ns e) 
      = let (fvs, e') = annotate e
        in (fvs \\ ns, Alt c ns e')

-- Printing lambda-calculus terms

printDef :: Def -> Doc
printDef (name, body) = hang (text name <+> text "=") 2 (printExpr body) 

printExpr :: Expr -> Doc
printExpr (Abs var fvs e) = text "\\" <> text var <+> braces (hsep (punctuate comma (texts fvs))) <>  text "." <+> printExpr e
printExpr (App e1 e2) = printVar e1 <+> printVar e2
printExpr (Var v) = text v
printExpr (Case e alts) = hang (text "case" <+> printExpr e <+> text "of") 2 (vcat' . map printAlt $ alts)
  where
    printAlt (Alt cons vs e) = text cons <+> (hsep (texts vs)) <+> text "->" <+> printExpr e
printExpr (Constr cons exprs) = text cons <+> (hsep . map printVar $ exprs)

printVar (Var v) = text v
printVar e = parens (printExpr e)

-- Pretty printing programs
printProgM :: ProgM C C -> Doc
printProgM = vcat' . maybeGraph empty printBlock
  where
    printBlock = p . blockToNodeList'
      where p (e, bs, x) = hang (maybeC empty printStmtM e) 2
                                (vcat' (map printStmtM bs) $+$
                                       maybeC empty printStmtM x)
 
printStmtM :: StmtM e x -> Doc
printStmtM (Bind n b) = text n <+> text "<-" <+> nest 2 (printTailM b)
printStmtM (Entry f args _ ) = text f <> parens (commaSep text args) <> text ":" 
printStmtM (CaseM v alts) = hang (text "case" <+> text v <+> text "of") 2 (vcat' $ map printAlt alts)
  where
    printAlt (Alt cons vs tailM) = text cons <+> hsep (texts vs) <+> text "->" <+> printTailM tailM
printStmtM (Done t) = printTailM t

printTailM :: TailM -> Doc
printTailM (Return n) = text "return" <+> text n
printTailM (Enter f a) = text f <+> text "@" <+> text a
printTailM (Closure f vs) = text "closure" <+> text f <+> braces (commaSep text vs)
printTailM (Call f vs) = text f <> parens (hsep (punctuate comma (texts vs)))
printTailM (ConstrM cons vs) = text cons <+> (hsep $ texts vs)

-- Pretty-printing utilities

vcat' :: [Doc] -> Doc
vcat' = foldl ($+$) empty

commaSep = punctuated comma 
spaced = punctuated space 
texts = map text

punctuated :: Doc -> (a -> Doc) -> [a] -> Doc
punctuated sep f = hcat . punctuate sep . map f

-- Hoopl utilities

maybeC :: a -> (n -> a) -> MaybeC e1 n -> a
maybeC _ f (JustC e) = f e
maybeC def f _ = def 

maybeO :: a -> (n -> a) -> MaybeO e1 n -> a
maybeO def f (JustO b) = f b
maybeO def f _ = def

maybeGraph :: b -> (forall e1 x1. block node e1 x1 -> b) -> Graph' block node e2 x2 -> [b]
maybeGraph b _ GNil = []
maybeGraph b f (GUnit block) = [f block]
maybeGraph b f (GMany entry middles exit) = maybeO b f entry :
                                        (map f . mapElems $ middles) ++
                                        [maybeO b f exit]

-- Testing

main = do 
  let pprint defs = putStrLn $ render $ vcat' (map printDef defs) $+$ printProgM (compileM defs)
  pprint [isnt, nil, notNil, compose
         , mapNot, myMap, applyNil]
  
prog = putStrLn . render . vcat'. map printDef . addFVs 

progM = putStrLn . render . printProgM . compileM 

abs :: Var -> (Expr -> Expr) -> Expr
abs v f = Abs v [] (f (Var v))

nil :: Def 
nil = ("nil", def)
  where
    def = abs "xs" $ \xs -> Case xs [Alt "Nil" [] true
                                       , Alt "Cons" ["a", "b"] false]
mapNot :: Def
mapNot = ("mapNot", def)
  where
    def = App (App (Var "myMap") 
                     (Var "not"))
          (mkCons (Constr "A" []) mkNil)

applyNil :: Def
applyNil = ("applyNil", def)
  where
    def = App (Var "nil") (Constr "Nil" [])

isnt :: Def
isnt = ("isnt", def)
  where
    def = abs "f" $ \f -> Case f [Alt "True" [] false
                                 , Alt "False" [] true]

notNil :: Def
notNil = ("notNil", def)
  where
    def = abs "xs" $ \xs -> App (Var "isnt") (App (Var "nil") xs)

compose :: Def
compose = ("compose", def)
  where
    def = abs "f" $ \f -> 
              abs "g" $ \g ->
              abs "x" $ \x -> App f (App g x)

myMap :: Def
myMap = ("myMap", def)
  where
    def = abs "f" $ \f ->
          abs "xs" $ \xs ->
          Case xs [Alt "Nil" [] mkNil
                  , Alt "Cons" ["x", "xs"] (mkCons (App f (Var "x"))
                                                   (App (App (Var "myMap") f)
                                                        (Var "xs")))]

mkCons :: Expr -> Expr -> Expr                                        
mkCons x xs = Constr "Cons" [x, xs]

mkNil :: Expr
mkNil = Constr "Nil" []

false :: Expr
false = Constr "False" []

true :: Expr
true = Constr "True" []


