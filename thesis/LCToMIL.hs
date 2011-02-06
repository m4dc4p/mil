{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module LCToMIL

where

import Control.Monad.State (State, execState, modify, gets)
import Text.PrettyPrint 
import Data.List (sort, nub)
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
               , compG :: (ProgM C C) -- ^ Program control-flow graph.
               , compT :: [Name] -- ^ top-level function names.
               , monadic :: [()] } -- ^ Allows nested monadic computation. Empty list means no, 
                                   -- anything else means yes.
               
type CompM = State CompS

instance UniqueMonad CompM where
  freshUnique = freshVal

compileStmtM :: Expr 
  -> (TailM -> CompM (ProgM O C))
  -> CompM (ProgM O C)

compileStmtM (EVar v) ctx 
  = ctx (Return v) `unlessMonad` ctx (Run v)

compileStmtM (EPrim _ _) _ 
  = error "EPrim should not appear unevaluated."

compileStmtM (ELit _) _ 
  = error "ELit statement not implemented."

compileStmtM (ECon cons _ exprs) ctx = 
  let compExpr vs [] = ctx (ConstrM cons (reverse vs))
      compExpr vs (e:es) = compVarM e $ \v -> 
                           compExpr (v:vs) es
  in compExpr [] exprs

compileStmtM (ELam v _ b) ctx = do
  let fvs = free b [v]
  f <- do
    prog <- compileStmtM b (return . mkLast . Done)
    name <- newTop "absBody"
    cloDefn name v fvs prog 
  ctx (Closure f fvs)

compileStmtM (ELet _ _) _ 
  = error "ELet statement not implemented."

compileStmtM (ECase e lcAlts) ctx = do
  let alts = map toAlt lcAlts
      altMonadic = any isMonadic (map altE alts)
  pushWhen altMonadic
  r <- fresh "result"
  f <- ctx (Return r) >>= callDefn "caseJoin" 
  let compAlt (Alt cons vs body) = do
        body' <- compileStmtM body (mkBind r f) >>= callDefn ("altBody" ++ cons)
        return (Alt cons vs body')
  altsM <- mapM compAlt alts
  popWhen altMonadic
  compVarM e $ \v -> return (mkLast (CaseM v altsM))
  where
    callDefn :: String -> ProgM O C -> CompM TailM
    callDefn name body = do 
      f <- newTop name
      ts <- gets compT
      dest <- blockDefn f [] body
      return (Goto dest [])

compileStmtM (EApp e1 e2) ctx 
  = 
    let pure ctx = compVarM e1 $ \f ->
                   compVarM e2 $ \g ->
                     ctx (Enter f g)
        monad ctx = pure $ \t -> do
                  v <- fresh "v"
                  rest <- ctx (Run v)
                  return (mkMiddle (v `Bind` t) <*> rest)
    in pure ctx `unlessMonad` monad ctx

compileStmtM (EFatbar _ _) _ 
  = error "EFatbar not implemented."

compileStmtM (EBind v _ b r) ctx = do
  pushMonad
  let fvs = nub (free b [] ++ free r [v])
  command <- do
    rest <- compileStmtM r (return . mkLast . Done)
    prog <- compileStmtM b $ \body -> 
            return (mkMiddle (v `Bind` body) <*> rest)
    name <- newTop "monBody"
    monDefn name fvs prog
  popMonad
  ctx (Thunk command fvs)

monDefn :: Name -> [Name] -> ProgM O C -> CompM Dest
monDefn = undefined

compVarM :: Expr 
  -> (Name -> CompM (ProgM O C))
  -> CompM (ProgM O C)
compVarM (EVar v) ctx = ctx v
compVarM (EPrim p _) ctx = ctx p
compVarM (ELit _) _ = error "ELit not implemented."
compVarM e ctx = compileStmtM e $ \t -> do
  v <- fresh "v"
  rest <- ctx v
  return (mkMiddle (v `Bind` t) <*> rest)

mkBind r f t = return (mkMiddle (Bind r t) <*> mkLast (Done f))

free :: Expr -> [Name] -> [Name]
free = undefined
      
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
  
-- | Add a name to the list of top-level functions.
addName :: Name -> CompM ()
addName name = modify (\s@(C { compT }) -> s { compT = name : compT })

-- | Push monadic compilation "mode" to stack
pushMonad :: CompM ()
pushMonad = 
  let f s@(C { monadic }) = s { monadic = () : monadic }
  in modify f

-- | Pop monadic compilation "mode" from stack
popMonad :: CompM ()
popMonad = 
  let f s@(C { monadic }) = s { monadic = drop 1 monadic }
  in modify f

-- | Are we in monadic compilatino mode?
inMonad :: CompM Bool
inMonad = 
  let f s@(C { monadic }) = null monadic
  in gets f

-- Run the left compilation, unless we
-- are compiling monadically. Run the right
-- in that case.
unlessMonad :: CompM (ProgM O C)
        -> CompM (ProgM O C)
        -> CompM (ProgM O C)
unlessMonad pure monad = 
  inMonad >>= \b -> if b then monad else pure

pushWhen :: Bool -> CompM ()
pushWhen True = pushMonad
pushWhen _ = return ()

popWhen :: Bool -> CompM ()
popWhen True = popMonad
popWhen _ = return ()

isMonadic :: Expr -> Bool
isMonadic (EBind _ _ _ _) = True
isMonadic (ELet _ expr) = isMonadic expr
isMonadic (ECase _ alts) = any isMonadic (map (altE . toAlt) alts)
isMonadic _ = False

toAlt :: LC.Alt -> Alt Expr
toAlt (LC.Alt cons _ vs expr) = Alt cons vs expr