{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module L3ToMil

where

import Control.Monad.State (State, execState, modify, gets)
import Text.PrettyPrint 
import Data.List (sort)
import Data.Maybe (fromMaybe, isJust, catMaybes)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Compiler.Hoopl

import MIL
import Lambda3
import Util

-- | Compiler state. 
data CompS = C { compI :: Int -- ^ counter for fresh variables
               , compG :: (ProgM C C) -- ^ Program control-flow graph.
               , compT :: [Name] } -- ^ top-level function names.
               
type CompM = State CompS

instance UniqueMonad CompM where
  freshUnique = freshVal

-- Compiling from lambda-calculus to the monadic language.

compileM :: [Name] -> Int -> Def -> (Int, ProgM C C)
compileM tops labelSeed def = 
  let result = foldr compDef initial $ prepareExpr tops [def]
  in (compI result + 1, compG result)
  where
    compDef p = execState (uncurry newDefn p)
    initial = C labelSeed emptyClosedGraph tops
    -- | Creates a new function definition
    -- using the arguments given and adds it
    -- to the control flow graph.    
    newDefn :: Name -> Expr -> CompM ()
    newDefn name (Abs v fvs b) = do
      prog <- compileStmtM b (return . mkLast . Done)
      cloDefn name v fvs prog >> return ()
    newDefn name body = do
      prog <- compileStmtM body (return . mkLast . Done)
      blockDefn name [] prog >> return ()

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
        body' <- compileStmtM body (mkBind r f) >>= callDefn ("altBody" ++ cons)
        return (Alt cons vs body')
  altsM <- mapM compAlt alts
  compVarM e $ \v -> return (mkLast (CaseM v altsM))
  where
    callDefn :: String -> ProgM O C -> CompM TailM
    callDefn name body = do 
      f <- newTop name
      ts <- gets compT
      dest <- blockDefn f [] body
      return (Goto dest [])

compileStmtM (Abs v fvs b) ctx = do
  f <- do
    prog <- compileStmtM b (return . mkLast . Done)
    name <- newTop "absBody"
    cloDefn name v fvs prog 
  ctx (Closure f fvs)

compileStmtM (Constr cons exprs) ctx = 
  let compExpr vs [] = ctx (ConstrM cons (reverse vs))
      compExpr vs (e:es) = compVarM e $ \v -> 
                           compExpr (v:vs) es
  in compExpr [] exprs


mkBind r f t = return (mkMiddle (Bind r t) <*> mkLast (Done f))
      
compVarM :: Expr 
  -> (Name -> CompM (ProgM O C))
  -> CompM (ProgM O C)
compVarM (Var v) ctx = ctx v
compVarM e ctx       = compileStmtM e $ \t -> do
  v <- fresh "v"
  rest <- ctx v
  return (mkMiddle (v `Bind` t) <*> rest)

-- | Add a name to the list of top-level functions.
addName :: Name -> CompM ()
addName name = modify (\s@(C { compT }) -> s { compT = name : compT })

-- | Make a new top-level function name, based on the
-- prefix given.
newTop :: Name -> CompM Name
newTop name = do
  f <- fresh name
  addName f
  return f

-- | Add a new block.
blockDefn :: Name -> [Name] -> ProgM O C -> CompM Dest
blockDefn name args progM = withNewLabel $ \l -> do
  addProg (mkFirst (BlockEntry name l args) <*> progM)
  return (name, l)
  
-- | Add a new closure-capturing block.
cloDefn :: Name -> Name -> [Name] -> ProgM O C -> CompM Dest
cloDefn name arg clos progM 
  | not (isCapture progM) = withNewLabel $ \l -> do
                          let args = clos ++ [arg]
                          dest <- blockDefn ("block" ++ name) args progM
                          addProg (mkFirst (CloEntry name l clos arg) <*>
                                   mkLast (Done (Goto dest args)))
                          return (name, l)
  | otherwise = withNewLabel $ \l -> do
                  addProg (mkFirst (CloEntry name l clos arg) <*> progM)
                  return (name, l)
  where
    isCapture :: ProgM O C -> Bool
    isCapture (GMany (JustO block) _ _ ) = 
      case blockToNodeList' block of
        (_, [], (JustC (Done (Closure _ _)))) -> True
        _ -> False

-- | Add a program (C C block) to the list of blocks
-- maintained by the monad.
addProg :: ProgM C C -> CompM ()
addProg block = modify (\s@(C { compG }) -> s { compG = block |*><*| compG })

-- | Do something with a new label.
withNewLabel :: UniqueMonad m => (Label -> m a) -> m a
withNewLabel f = freshLabel >>= f
  
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

printProgM :: ProgM C C -> Doc
printProgM = vcat' . maybeGraphCC empty printBlockM

printBlockM = p . blockToNodeList'
  where p (e, bs, x) = hang (maybeC empty printStmtM e) 2
                       (vcat' (map printStmtM bs) $+$
                        maybeC empty printStmtM x)
