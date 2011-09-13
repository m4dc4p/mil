{-# LANGUAGE GADTs, RankNTypes, TypeFamilies
  , FlexibleInstances, ScopedTypeVariables #-}

import Compiler.Hoopl

collapse :: Graph StmtM C C -> Graph StmtM C C
collapse body = 
  let opt = runInfinite $ do
        (p, _, _) <- analyzeAndRewriteFwd fwd (undefined :: MaybeC C [Label]) body undefined
        return p
      fwd = FwdPass { fp_lattice = undefined
                    , fp_transfer = undefined
                    , fp_rewrite = iterFwdRw (mkFRewrite rewriter)  }
      rewriter :: (FuelMonadT m, FuelMonad (m (StateX Bool))) => forall e x. StmtM e x -> () -> (m (StateX Bool)) (Maybe (Graph StmtM e x))
      rewriter Done col = do
        f <- liftFuel getX
        liftFuel (setX (not f))
        return Nothing
  in fst $ (runStateX opt) True

newtype StateX s a = X { runStateX :: s -> (a, s) }
instance Monad (StateX s) where
  f >>= a = bindX f a
  return a = returnX a

bindX :: StateX s a -> (a -> StateX s b) -> StateX s b
bindX (X m) f = X $ \s ->
  let (a, s') = m s
      (X m') = f a
  in m' s'

returnX :: a -> StateX s a
returnX a = X $ \s -> (a, s)

setX :: s -> StateX s ()
setX s = X $ \_ -> ((), s)

getX :: StateX s s
getX = X $ \s -> (s, s)

runInfinite :: (Monad m) => InfiniteFuelMonad m a -> m a
runInfinite fm = runWithFuel infiniteFuel $ fm

runChecked :: (Monad m) => Fuel -> CheckingFuelMonad m a -> m a
runChecked fuel fm = runWithFuel fuel $ fm

instance CheckpointMonad (StateX s) where
  type Checkpoint (StateX s) = s
  checkpoint = checkpointX
  restart = restartX

checkpointX :: StateX s s
checkpointX = X $ \s -> (s, s)

restartX :: s -> StateX s ()
restartX s = X $ \_ -> ((), s)

data StmtM e x where
  Done :: StmtM O C

instance NonLocal StmtM where
  entryLabel = undefined
  successors = undefined


