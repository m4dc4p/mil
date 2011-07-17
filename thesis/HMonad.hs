{-# LANGUAGE GADTs, RankNTypes, TypeFamilies
  , FlexibleInstances, ScopedTypeVariables #-}

import Compiler.Hoopl

collapse :: Graph StmtM C C -> Graph StmtM C C
collapse body = 
  let f = runStateX $ do
        (p, _, _) <- analyzeAndRewriteFwd fwd (undefined :: MaybeC C [Label]) body undefined
        return p
      fwd = FwdPass { fp_lattice = undefined
                    , fp_transfer = undefined
                    , fp_rewrite = iterFwdRw (mkFRewrite rewriter)  }
      rewriter :: forall e x. StmtM e x -> () -> StateX (Fuel, Int) (Maybe (Graph StmtM e x))
      rewriter Done col = do
                        (f, z) :: (Fuel, Int) <- getX
                        f :: Fuel <- getFuelX
                        f <- getFuel
                        setFuel f
                        setX (f, z)
                        return Nothing
  in fst $ f (1, 100) 

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

instance FuelMonad (StateX (Fuel, s)) where
  getFuel = getFuelX
  setFuel = setFuelX

getFuelX :: StateX (Fuel,s) Fuel
getFuelX = X $ \(f, s) -> (f, (f,s))

setFuelX :: Fuel -> StateX (Fuel, s) ()
setFuelX f = X $ \(_,s) -> ((), (f,s))

instance CheckpointMonad (StateX (Fuel, s)) where
  type Checkpoint (StateX (Fuel, s)) = (Fuel, s)
  checkpoint = checkpointX
  restart = restartX

checkpointX :: StateX (Fuel, s) (Fuel, s)
checkpointX = X $ \(f, s) -> ((f,s), (f,s))

restartX :: (Fuel, s) -> StateX (Fuel, s) ()
restartX (f, s) = X $ \_ -> ((), (f, s))

data StmtM e x where
  Done :: StmtM O C

instance NonLocal StmtM where
  entryLabel = undefined
  successors = undefined


