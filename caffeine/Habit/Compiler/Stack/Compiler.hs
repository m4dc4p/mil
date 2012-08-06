module Habit.Compiler.Stack.Compiler

where

import Data.List (nub, lookup, intercalate, elemIndex)
import Data.Function (on)
import Control.Monad.Writer
import Control.Monad.State
import Data.Maybe (catMaybes)
import Data.Supply
import Debug.Trace
import Data.Graph.SCC(stronglyConnComp)
import Data.Graph(SCC(..))

import Habit.Syntax.AST
import Habit.Syntax.Names (Name(..), qual)
import qualified Habit.Syntax.Utils as Utils
import Habit.Syntax.IFace

import Habit.Compiler.Stack.Machine (Instr)
import qualified Habit.Compiler.Stack.Machine as H -- H for hardware

{-| Values can be found in stack position (StackV) or an "address" of
some value in a data structure on the stack (Field).

Note that stack position is measured from the bottom of the stack, starting
at 0.
 -}
data EnvLoc = StackV { stackOffset :: Int }
            | Field { stackLoc :: EnvLoc
                    , dataOffset :: Int }
  deriving Show

type Env = [(Name, EnvLoc)]
type LabelC = Int
type Code = (LabelC, [Instr])
type Labels = Supply LabelC

-- | ST tracks the number of items that
-- have been added to the stack. ST grows from 0 up - so
-- the bottom of the stack is always 0.
type ST = Int -- for help tracking the top of the stack

-- | What to do when a match fails. In the Goto case, the first
-- argument represents the label which resets the stack before jumping
-- to the label in the second argument
data OnFail = Abort 
   | OnFail LabelC
 deriving (Show)

-- Match expression compilation strategy
data MState = MState { nextLabel :: Labels }

type M = StateT MState (Writer [Code])

compile :: Labels -> Module -> [Instr]
compile supply (Module { mod_decls = decls 
                       , mod_name = mod_name
                       , mod_data = datas }) 
    = let ((env, code), blocks) = runCompiler (orderDecls decls) s1 
          mainN = qual mod_name "main"
          mainC = maybe [] (\l -> [H.PushL (convLoc l), H.Halt]) (lookup mainN env) 
      in code ++ mainC ++ concatMap mkBody blocks
  where
    -- Place module data constructors into
    -- the initial environment
    (s1, s2) = split2 supply
    mkBody (label, code) = mkLabel label : code ++ [H.Ret]
    runCompiler code s = runWriter $ (compileTop [] 0 datas code) `evalStateT` (MState s)

compileTop :: Env -> ST -> [Data] -> [ImplDecl] -> M (Env, [Instr])
compileTop env st datas decls = do
  (st', env', datasC) <- compileDatas env st datas
  (env'', declsC) <- compileDecls env' st' decls
  return (env'', datasC ++ declsC)

-- | Compile a list of declarations.
compileDecls :: Env -> ST -> [ImplDecl] -> M (Env, [Instr])
compileDecls env st decls = do
  let cdM (s, e, is) d = do
        -- Compile an individual declaration and label
        -- it.
        (e', is') <- compileDecl e s d
        return (s + 1, e', is ++ is')
  (_, e, is) <- foldM cdM (st, env, []) decls
  return (e, is)

-- | Compile each constructor to a function which will
-- create that data.
compileDatas :: Env -> ST -> [Data] -> M (ST, Env, [Instr])
compileDatas env st dataDefs = do
    let mkData _ 1 (name, count) = do
          let locs = map (convLoc . Field cloLoc) [0..count - 2] ++ [convLoc argLoc]
          return $ H.AllocD (showName name) count :
             zipWith H.Copy locs (map (convLoc . Field (StackV 2)) [0..])
        mkData size remain def  = do
          l <- newLabel
          c <- mkData (size + 1) (remain - 1) def
          tell [(l, c)]
          return $ [H.Note "mkData n"
                   , mkClosure l size]
        compileData (s, e, is) (name, 0) = do
          return $ (s + 1, (name, StackV s) : e, is ++ 
                   [H.Note ("compileData 0: " ++ show s ++ ": " ++ showName name)
                   , H.AllocD (showName name) 0])
        compileData (s, e, is) (name, count) = do
          l <- newLabel
          bodyC <- mkData 0 count (name, count)
          tell [(l, bodyC)]
          return (s + 1, (name, StackV s) : e, is ++ 
                 [H.Note ("compileData n: " ++ show s ++ ": " ++ showName name)
                 , H.AllocC (lc2lv l) []])
    foldM compileData (st, env, []) constructors
  where
    constructors = map mkPair . concatMap data_cons $ dataDefs
    countFields = length . qual_body . data_con_fields 
    mkPair con = (data_con_name con, countFields con)


-- | Compile an individual implementation
-- declaration.
compileDecl :: Env -> ST -> ImplDecl -> M (Env, [Instr])
compileDecl env st (ImplDecl { decl_name = name
                                , decl_body = body }) 
    = do 
  let env' = (name, StackV st) : env
  matchC <- compileMAbs env' (st + 1) Abort body
  return $ (env'
           , H.Note ("compileDecl: " ++ show st ++ ": " ++ showName name) : matchC)

type Success = [Instr]

-- | Top level match compilation
compileMatch :: Env -> ST -> Success -> OnFail -> Match -> [EnvLoc] -> M [Instr]
compileMatch env st success failure (MPat pat body) (arg:args) = do
  (env', patC) <- compilePat env st failure pat arg
  bodyC <- compileMatch env' (st + 1) [] failure body args
  return $ H.Note "compileMatch: MPat" : patC ++ bodyC ++ success

compileMatch env st success failure (MGrd guard body) (arg:args) = do
  (e', guardC) <- compileGuard env st failure guard arg 
  bodyC <- compileMatch e' (st + 1) [] failure body args
  return $ H.Note "compileMatch: MGrd" : guardC ++ bodyC ++ success

compileMatch env st success failure (MAlt alt1 alt2) args = do
  l1 <- newLabel
  l2 <- newLabel
  alt1C <- compileMatch env st [] (OnFail l2) alt1 args
  alt2C <- compileMatch env st [H.Jmp (lc2lv l1)] failure alt2 args
  tell [(l2, [H.MatchFailure] ++ alt2C)]
  -- MatchEnd *must* come before the label here, because we do 
  -- not want the alternative match to trigger MatchEnd. If
  -- the alternative has executed, then MatchFailure has executed
  -- and MatchEnd should not execute.
  return $ H.MatchStart : alt1C ++ H.MatchEnd : mkLabel l1 : success

compileMatch env st success failure (MExp expr) _ = do
  exprC <- compileExpr env st failure expr
  return $ (H.Note "compileMatch: MExp" : exprC ++ success)

compilePat :: Env -> ST -> OnFail -> Pat -> EnvLoc -> M (Env, [Instr])
compilePat env st failure (PVar name) arg = do
  let note = [H.Note ("compilePat: PVar (" ++ showName name ++ 
                    " : " ++ show arg ++ ")")]
  return ((name, arg) : env, note)

compilePat env st failure (PCon name _ pats) arg = do
  let f (loc, s, env, is) p = do
        (e', is') <- compilePat env s failure p loc
        return (nextPtr loc, s + 1, e', is ++ is')
  (_, _, env', patC) <- foldM f (newPtrArg arg, st, env, []) pats
  l1 <- newLabel
  let failC = handleFailure failure 
  tell [(l1, failC)]
  return $ (env', H.Note "compilePat: PCon" : patC ++ 
           [H.FailT (convLoc arg) (showName name) (lc2lv l1)])

compilePat env st failure (PGrd pat guard) arg = do
  (env', guardC) <- compileGuard env st failure guard arg
  (env'', patC) <- compilePat env' (st + 1) failure pat arg
  return $ (env'', H.Note "compilePat: PGrd" : guardC ++ patC)

compilePat env st failure (PSig pat typ) arg = do
  (env', patC) <- compilePat env st failure pat arg
  return $ (env', H.Note "compilePat: PSig" : patC)

compilePat env _ _ PWild _ = return (env, [H.Note "compilePat: PWild"])

compileGuard :: Env -> ST -> OnFail -> Guard -> EnvLoc -> M (Env, [Instr])
compileGuard env st failure (GMatch pat expr) arg = do
  exprC <- compileExpr env st failure expr
  (e', testC) <- compilePat env (st + 1) failure pat arg 
  return $ (e', H.Note "compileGuard" : exprC ++ testC)
compileGuard env st failure (GLet decls) arg = do
  (e', is) <- compileDecls env st (orderDecls decls)
  return $ (e', H.Note "compileDecls" : is)

-- | Compile an expression.
compileExpr :: Env -> ST -> OnFail -> Expr -> M [Instr]
compileExpr env st failure (EApp expr1 expr2) = do
  expr2C <- compileExpr env st failure expr2
  expr1C <- compileExpr env (st + 1) failure expr1
  return $ H.Note "EApp" : expr2C ++ expr1C ++ [H.Enter]
compileExpr env st failure (ELet decls expr) = do
  (env', declC) <- compileDecls env st (orderDecls decls)
  exprC <- compileExpr env' (st + (length $ declsToList decls)) failure expr
  return $ H.Note "ELet" : declC ++ exprC
compileExpr env st failure (EAbs match) = do
  code <- compileMAbs env st failure match
  return $ H.Note "EAbs" : code
compileExpr env st failure(ECase expr match) = do
  exprC <- compileExpr env st failure expr
  matchC <- compileMAbs env (st + 1) failure match
  return $ H.Note "ECase" : exprC ++ matchC
compileExpr env st failure (EInfix expr1 name expr2) = do
  expr1C <- compileExpr env st failure expr1
  expr2C <- compileExpr env (st + 1) failure expr2
  return $ case lookup name env of
               Just l -> [H.Note $ "EInfix: " ++ showName name
                         , H.PushL (convLoc l)]
               _ -> error $ "Can't lookup infix name " ++ showName name
compileExpr env st failure (EParens expr) = do
  exprC <- compileExpr env st failure expr
  return $ H.Note "EParens" : exprC
compileExpr env st failure (EVar x) = compileEVar env x
compileExpr _ _ _ (ELit literal) = return [H.PushV . H.LitV . showLit $ literal]
  where
    showLit (LNum i) = show i
    showLit (LFrac r) = show r
    showLit (LChar c) = [c]
    showLit (LString s) = s

compileEVar env (EV name types evs) = do
  return $ case lookup name env of
             Just l -> [H.Note ("EVar: " ++ showName name)
                       , H.PushL (convLoc l)]
             _ -> error $ "Can't lookup var name " ++ showName name

-- | The EnvLoc value returned is the location of the 
-- abstraction value on the stack.
compileMAbs :: Env -> ST -> OnFail -> Match -> M [Instr]
compileMAbs env st failure match = do
  -- Remove constructors because they mess up lookups later.
  let compileAbs size 1 = do
        let args = [Field cloLoc i | i <- [0 .. size - 1]] ++ [argLoc]
            env' = zip fvs args ++ env
        matchC <- compileMatch env' (st + params) [] failure match (drop nfvs args)
        return $ H.Note "compileAbs 1" : matchC
      compileAbs size remain = do
        l <- newLabel
        bodyC <- compileAbs (size + 1) (remain - 1)
        tell [(l, bodyC)]
        return $ [H.Note "compileAbs _ _"
                 , mkClosure l size]
      fvs = Utils.fvs match 
      nfvs = length fvs
      params = numParams match
  case params of
    0 -> do
      matchC <- compileMatch env st [] failure match []
      return $ H.Note "compileMAbs 0" : matchC
    n -> do
      l <- newLabel
      bodyC <- compileAbs nfvs n
      tell [(l, bodyC)]
      return $ [H.Note "compileMAbs n" 
               , H.AllocC (lc2lv l) (fvClosure fvs env)]

-- | Make a new closure based on values found in 
-- closure and arg positions. Size represents the number of values
-- in the source closure. The stack size must be given
-- so the destinatin can be addressed when it is allocated.
mkClosure :: LabelC -> Int -> Instr
mkClosure label size = 
    let mkLocs s = map (convLoc . Field s)  [0 .. size - 1]
    in H.AllocC (lc2lv label) (mkLocs cloLoc ++ [convLoc argLoc]) 

-- | Copy the names given to the closure found at
-- dst. Names are copied starting at 0 in the closure.
fvClosure :: [Name] -> Env -> [H.Loc]
fvClosure free env = [convLoc l | (Just l) <- map (flip lookup env) free]

handleFailure :: OnFail -> [Instr]
handleFailure Abort = [H.MatchFailure]
handleFailure (OnFail l2) = [H.Jmp (lc2lv l2)]

-- | Convert an environment location to a stack
-- location.
convLoc (StackV o) = H.Stack o
convLoc (Field o f) = H.Field (convLoc o) f

-- | Increment the stack location argument. Only works for value
-- locations, not references.
nextArg (StackV o) = (StackV (o + 1))
nextArg l = error $ "Can't stack incremenet " ++ show l

-- | Generates a location which will addresses structured
-- data. 
newPtrArg l = Field l 0

-- | Increments a data location argument (leaves stack alone)
nextPtr l@(StackV o) = Field l 0
nextPtr (Field o ref) = Field o (ref + 1)

-- | Get a new label for match failure
newLabel :: M LabelC
newLabel = do
  m <- get
  let (s1, s2) = split2 . nextLabel $ m
  put m { nextLabel = s2 }
  return (supplyValue s1)

showName (Name (Just m) name _) = mkPrefix m ++ "." ++ name
  where
    mkPrefix (ModName [] last) = last
    mkPrefix (ModName pres last) = foldr1 (\a rest -> a ++ "." ++ rest) pres ++ "." ++ last
showName (Name _ name _) = name

mkLabel :: LabelC -> Instr
mkLabel = H.Label . show

lc2lv :: LabelC -> H.Label
lc2lv = show

-- | Calculate maximum parameters required
-- by a match.
numParams :: Match -> Int
numParams (MPat _ m) = 1 + numParams m
numParams (MGrd _ m) = numParams m
numParams (MAlt m1 m2) = max (numParams m1) (numParams m2)
numParams _ = 0

showEnv :: Env -> String
showEnv env = concatMap (\(n, l) -> ("(" ++ showLoc l ++ ", " ++ showName n ++ ")") ++ ",") env

showLoc (Field l o) = showLoc l ++ "[" ++ show o ++ "]"
showLoc (StackV o) = "S[" ++ show o ++ "]"

-- | Closure for a function always
-- at the top of the stack, initially.
cloLoc = StackV 1

-- | Argument for a function always
-- at the bottom of the stack
argLoc = StackV 0

declsToList :: Decls -> [ImplDecl]
declsToList decls = map decl (expl_decls decls) ++ impl_decls decls

-- | Order declarations by dependencies. "Root" declarations
-- will come first in the list. Thanks to Iavor for this one.
orderDecls :: Decls -> [ImplDecl]
orderDecls ds = concat [d | (CyclicSCC d) <- sccs] ++ [ d | (AcyclicSCC d) <- sccs ]
  where
    sccs = stronglyConnComp $ zipWith to_edge decls [0..]
    decls = map decl (expl_decls ds) ++ impl_decls ds
    defs = [decl_name d | d <- decls ]
    to_edge d n = (d, n, catMaybes $ map (`elemIndex` defs) $ nub $ Utils.fvs d)
