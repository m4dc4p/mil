{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module LCToMIL

where

import Control.Monad.State (State, execState, modify, gets, get)
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
               , monadic :: [()] } -- ^ Allows nested monadic computation. Empty list means no, 
                                   -- anything else means yes.
               
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
    foldr (|*><*|) predefined . snd . foldr compileEach (100, []) $ defs
  where
    tops = primNames  ++ userTops
    compileEach :: Def -> (Int, [ProgM C C]) -> (Int, [ProgM C C])
    compileEach p (i, ps) = 
      let (j, p') = compileM tops i p
      in (j, p' : ps)

compileM :: [Name] -> Int -> Def -> (Int, ProgM C C)
compileM tops labelSeed def = 
  let result = foldr compDef initial [def]
  in (compI result + 1, compG result)
  where
    compDef p = execState (uncurry newDefn p)
    initial = C labelSeed emptyClosedGraph tops []
    -- | Creates a new function definition
    -- using the arguments given and adds it
    -- to the control flow graph.    
    newDefn :: Name -> Expr -> CompM ()
    newDefn name (ELam v _ b) = do
      let fvs = v `delete` free b \\ tops
      prog <- compileStmtM b (return . mkLast . Done)
      cloDefn name v fvs prog >> return ()
    newDefn name body = do
      prog <- compileStmtM body (return . mkLast . Done)
      blockDefn name [] prog >> return ()

compileStmtM :: Expr 
  -> (TailM -> CompM (ProgM O C))
  -> CompM (ProgM O C)

compileStmtM (EVar v) ctx 
  = ctx (Return v) `unlessMonad` ctx (Run v)

compileStmtM (EPrim _ _) _ 
  = error "EPrim in compileStmtM."

compileStmtM (ELit (Lit n _)) ctx
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
      dest <- blockDefn f [] body
      return (Goto dest [])

compileStmtM (EApp e1 e2) ctx 
  = compVarM e1 $ \f ->
    compVarM e2 $ \g ->
      ctx (Enter f g)

compileStmtM (EFatbar _ _) _ 
  = error "EFatbar not implemented."

compileStmtM (EBind v _ b r) ctx = do
  rest <- compileStmtM r ctx
  compileStmtM b $ \body -> do
    t <- fresh "t"
    return (mkMiddle (t `Bind` body) <*> 
            mkMiddle (v `Bind` (Run t)) <*> 
            rest)

primDefn :: Name 
         -> Int 
         -> (Name -> CompM (ProgM O C)) 
         -> CompM (ProgM O C)
primDefn p 1 ctx = do 
  dest <- blockDefn p [] (mkLast . Done $ Prim p [])
  ctx p
primDefn p n ctx = do
  let vs = take (n - 1) $ zipWith (++) (repeat "e") (map show [1..])
  dest <- blockDefn p vs (mkLast . Done $ Prim p vs)
  ctx p

  
primDefined :: Name -> CompM Bool
primDefined p = return False

compVarM :: Expr 
  -> (Name -> CompM (ProgM O C))
  -> CompM (ProgM O C)
compVarM (EVar v) ctx = ctx v
compVarM e ctx = compileStmtM e $ \t -> do
  v <- fresh "v"
  rest <- ctx v
  return (mkMiddle (v `Bind` t) <*> rest)

mkBind r f t = return (mkMiddle (Bind r t) <*> mkLast (Done f))

free :: Expr -> Free
free = nub . free'
  where
    free' (EVar v) = [v]
    free' (EPrim v _) = []
    free' (ELit _) = []
    free' (ECon _ _ expr) = nub (concatMap free' expr)
    free' (ELam v _ expr) = v `delete` nub (free' expr)
    free' (ELet _ _) = error "ELet free'."
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

-- | Are we in monadic compilation mode?
inMonad :: CompM Bool
inMonad = 
  let f s@(C { monadic }) = not (null monadic)
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

-- prims :: Expr -> [Name]
-- prims e = nub (prims' [] e)
--   where
--     prims' acc (EVar _) = acc
--     prims' acc (EPrim p _) = p : acc
--     prims' acc (ELit _) = acc
--     prims' acc (ECon _ _ exprs) = concatMap (prims' []) exprs ++ acc
--     prims' acc (ELam _ _ e) = prims' acc e
--     prims' acc (ELet _ _) = error "prims ELet"
--     prims' acc (ECase e alts) = concatMap (prims' []) (map (\(LC.Alt _ _ _ e) -> e) alts) ++ prims' acc e
--     prims' acc (EApp e1 e2) = prims' acc e1 ++ prims' acc e2
--     prims' acc (EFatbar e1 e2) = prims' acc e1 ++ prims' acc e2
--     prims' acc (EBind _ _ e1 e2) = prims' acc e1 ++ prims' acc e2
                                                                                                                                                                                                                                   