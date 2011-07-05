{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module LCToMIL

where

import Control.Monad.State (State, execState, modify, gets, get, put)
import Text.PrettyPrint 
import Data.List (sort, nub, delete, (\\))
import Data.Maybe (fromMaybe, isJust, catMaybes)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Compiler.Hoopl

import MIL
import Syntax.LambdaCase hiding (Alt)
import qualified Syntax.LambdaCase as LC
import Util

-- | Compiler state. 
data CompS = C { compI :: Int -- ^ counter for fresh variables
               , compG :: ProgM C C -- ^ Program control-flow graph.
               , compT :: [Name] -- ^ top-level function names.
               , compM :: (Bool, [Bool]) } -- ^ Allows nested
                                             -- monadic
                                             -- computation. "Top"
                                             -- value indicates if we
                                             -- are compiling
                                             -- monadically or
                                             -- not. List serves as a
                                             -- stack of previous
                                             -- states. Starts non-monadic (False, []).

-- | Create the initial state for our compiler.
mkCompS i tops = C i emptyClosedGraph tops (False, [])
               
type CompM = State CompS
type Free = [Name]

instance UniqueMonad CompM where
  freshUnique = freshVal

type Def = (Name, Expr)

type CompP = State ([Name], ProgM C C, Int)
instance UniqueMonad CompP where
  freshUnique = do
    (_, _, i) <- get
    modify (\(n, g, j) -> (n, g, j + 1))
    return (intToUnique i)

emptyPrelude :: ([Name], ProgM C C)
emptyPrelude = ([], emptyClosedGraph)

-- | Pre-compiled primitive functions
-- supporting monadic actions.
prelude :: ([Name], ProgM C C)
prelude = 
  let comp (name, impl) = do
        impl' <- impl
        (names, g, i) <- get
        modify (\(names, g, i) -> (name : names,  impl' |*><*| g, i))
        return ()
      (names, preludeProg, _) = foldr (\prim -> execState (comp prim)) ([], emptyClosedGraph, 0 :: Int) prims
  in (names, preludeProg)

compile :: [Name] -> ([Name], ProgM C C) -> [Def] -> ProgM C C
compile userTops (primNames, predefined) defs = 
    foldr (|*><*|) predefined . snd . foldr compileDef (100, []) $ defs
  where
    -- Compiles a single LC definition and returns the compiler
    -- state, to be used during the next definition.
    compileDef :: Def -> (Int, [ProgM C C]) -> (Int, [ProgM C C])
    compileDef p (i, ps) = 
      let result = execState (newDefn p) (mkCompS i (primNames  ++ userTops))
      in (compI result + 1, compG result : ps)

-- Creates a new function definition
-- using the arguments given and adds it
-- to the control flow graph.    
newDefn :: (Name, Expr) -> CompM ()
newDefn (name, (ELam v _ b)) = do
  tops <- gets compT
  let fvs = v `delete` free b \\ tops
  cloDefn name v fvs (\n l -> compileStmtM b (return . mkLast . Done n l)) 
  return ()

-- A monadic progam will always begin with EBind.
newDefn (name, body@(EBind v _ b r)) = do
  tops <- gets compT
  let fvs = v `delete` (nub (free b ++ free r) \\ tops)
  thunkDefn name fvs (\n l -> compileStmtM body (return . mkLast . Done n l))
  return ()

newDefn (name, body) = do
  blockDefn name [] (\n l -> compileStmtM body (return . mkLast . Done n l))
  return ()

compileStmtM :: Expr 
  -> (TailM -> CompM (ProgM O C))
  -> CompM (ProgM O C)

compileStmtM (EVar v _) ctx 
  = ctx (Return v) `unlessMonad` ctx (Run v)

compileStmtM (EPrim p _) ctx = error "EPrim in statement context."

compileStmtM (ENat n) ctx
  = ctx (LitM n)

compileStmtM (ECon cons _ exprs) ctx = 
  let compExpr vs [] = ctx (ConstrM cons (reverse vs))
      compExpr vs (e:es) = compVarM e $ \v -> 
                           compExpr (v:vs) es
  in compExpr [] exprs

compileStmtM e@(ELam v _ b) ctx = do
  tops <- gets compT
  let fvs = free e \\ tops
  f <- do
    name <- newTop "absBody"
    cloDefn name v fvs (\n l -> compileStmtM b (return . mkLast . Done n l))
  ctx (Closure f fvs)

compileStmtM (ELet (Decls defs) outerBody) ctx = compVars (concat defs) 
  where
    compVars [(name, _, letBody)] = 
      compVarM letBody $ \v -> do
        rest <- compileStmtM outerBody ctx
        return (mkMiddle (Bind name (Return v)) <*> rest)
    compVars ((name, _, letBody):ds) = do
      rest <- compVars ds 
      compVarM letBody $ \v -> do
        return (mkMiddle (Bind name (Return v)) <*> rest)

compileStmtM (ECase e lcAlts) ctx = do
  let alts = map toAlt lcAlts
  r <- fresh "result"
  f <- ctx (Return r) >>= \rest -> callDefn "caseJoin" (\n l -> return rest)
  let compAlt (Alt cons vs body) = do
        body' <- callDefn ("altBody" ++ cons) (\n l -> compileStmtM body (mkBind n l r f))
        return (Alt cons vs body')
  altsM <- mapM compAlt alts
  compVarM e $ \v -> return (mkLast (CaseM v altsM))
  where
    callDefn :: String -> (Name -> Label -> CompM (ProgM O C)) -> CompM TailM
    callDefn name body = do 
      f <- newTop name
      dest <- blockDefn f [] body
      return (Goto dest [])

compileStmtM (EApp e1 e2) ctx 
  = compVarM e1 $ \f ->
    compVarM e2 $ \g ->
      ctx (Enter f g)

compileStmtM (EBind v _ b r) ctx = do
  rest <- compileStmtM r ctx
  asMonadic (compVarM b $ \m -> do
               return (mkMiddle (v `Bind` (Run m)) <*> 
                       rest))

compileStmtM (EFatbar _ _) _ 
  = error "EFatbar not implemented."

compileStmtM (EBits _ _) _ 
  = error "EBits not implemented."

primDefn :: Name 
         -> Int 
         -> (Name -> CompM (ProgM O C)) 
         -> CompM (ProgM O C)
primDefn p 1 ctx = do 
  dest <- blockDefn p [] (\n l -> return . mkLast . Done n l $ Prim p [])
  ctx p
primDefn p n ctx = do
  let vs = take (n - 1) $ zipWith (++) (repeat "e") (map show [1..])
  dest <- blockDefn p vs (\n l -> return . mkLast . Done n l $ Prim p vs)
  ctx p

  
primDefined :: Name -> CompM Bool
primDefined p = return False

compVarM :: Expr 
  -> (Name -> CompM (ProgM O C))
  -> CompM (ProgM O C)
compVarM (EVar v) ctx = ctx v
compVarM (EPrim p _) ctx = ctx p
compVarM e ctx = compileStmtM e $ \t -> do
  v <- fresh "v"
  rest <- ctx v
  return (mkMiddle (v `Bind` t) <*> rest)

mkBind :: Name -> Label -> Name -> TailM -> TailM -> CompM (ProgM O C)
mkBind n l r f t = return (mkMiddle (Bind r t) <*> mkLast (Done n l f))

free :: Expr -> Free
free = nub . free'
  where
    free' (EVar v _) = [v]
    free' (EPrim v _) = []
    free' (ENat _) = []
    free' (EBits _ _) = []
    free' (ECon _ _) = []
    free' (ELam v _ expr) = v `delete` nub (free' expr)
    free' (ELet (Decls decls) expr) = free' expr \\ (map (\(n,_,_) -> n) $ concat decls)
    free' (ECase expr alts) = nub (free' expr ++ concatMap (\(LC.Alt _ _ vs e) -> nub (free' e) \\ vs) alts)
    free' (EApp e1 e2) = nub (free' e1 ++ free' e2)
    free' (EFatbar e1 e2) = nub (free' e1 ++ free' e2)
    free' (EBind v _ e1 e2) = nub (free' e1 ++ v `delete` nub (free' e2))

      
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

-- | Make a new top-level function name, based on the
-- prefix given.
newTop :: Name -> CompM Name
newTop name = do
  f <- fresh name
  addName f
  return f

thunkDefn :: Name -> [Name] -> (Name -> Label -> CompM (ProgM O C)) -> CompM Dest
thunkDefn name args progM = withNewLabel $ \m -> do
  dest <- blockDefn ("block" ++ name) args progM
  addProg (mkFirst (BlockEntry name m args) <*> mkLast (Done name m (Thunk dest args)))
  return (name, m)

-- | Add a new block.
blockDefn :: Name -> [Name] -> (Name -> Label -> CompM (ProgM O C)) -> CompM Dest
blockDefn name args progM = withNewLabel $ \l -> do
  rest <- progM name l
  addProg (mkFirst (BlockEntry name l args) <*> rest)
  return (name, l)
  
-- | Add a new closure-capturing block.
cloDefn :: Name -> Name -> [Name] -> (Name -> Label -> CompM (ProgM O C)) -> CompM Dest
cloDefn name arg clos progM = do
    withNewLabel $ \t -> do
      progTemp <- progM "foo" t
      if isCapture progTemp
       then captureDefn
       else nonCaptureDefn
  where
    captureDefn = withNewLabel $ \l -> do
      let args = clos ++ [arg]
      dest <- blockDefn ("block" ++ name) args progM
      addProg (mkFirst (CloEntry name l clos arg) <*>
               mkLast (Done name l (Goto dest args)))
      return (name, l)
    nonCaptureDefn = withNewLabel $ \l -> do
      rest <- progM name l
      addProg (mkFirst (CloEntry name l clos arg) <*> rest)
      return (name, l)
    isCapture :: ProgM O C -> Bool
    isCapture (GMany (JustO block) _ _ ) = 
      case blockToNodeList' block of
        (_, [], (JustC (Done _ _ (Closure _ _)))) -> True
        _ -> False

-- | Add a program (C C block) to the list of blocks
-- maintained by the monad.
addProg :: ProgM C C -> CompM ()
addProg block = modify (\s@(C { compG }) -> s { compG = block |*><*| compG })

-- | Do something with a new label.
withNewLabel :: UniqueMonad m => (Label -> m a) -> m a
withNewLabel f = freshLabel >>= f
  
-- | Add a name to the list of top-level functions.
addName :: Name -> CompM ()
addName name = modify (\s@(C { compT }) -> s { compT = name : compT })

-- | Run the compiler in monadic
-- mode. Restore the previous mode when finished.
asMonadic :: CompM a -> CompM a
asMonadic m = do
  modify (\s@(C _ _ _ (flag, stack)) -> s { compM = (True, flag : stack) })
  a <- m
  modify (\s@(C _ _ _ (_, (flag:stack))) -> s { compM = (flag,stack) })
  return a
  

-- | Are we in monadic compilation mode?
inMonad :: CompM Bool
inMonad = 
  let f s@(C { compM }) = fst compM
  in gets f

-- Run the left compilation, unless we
-- are compiling monadically. Run the right
-- in that case.
unlessMonad :: CompM (ProgM O C)
        -> CompM (ProgM O C)
        -> CompM (ProgM O C)
unlessMonad pure monad = 
  inMonad >>= \b -> if b then monad else pure

toAlt :: LC.Alt -> Alt Expr
toAlt (LC.Alt cons _ vs expr) = Alt cons vs expr

