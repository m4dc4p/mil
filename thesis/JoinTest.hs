{-# LANGUAGE GADTs, NoMonomorphismRestriction, RankNTypes #-}
module JoinTest

where

import Debug.Trace
import Compiler.Hoopl

data Stmt e x where
  Entry :: Label -> Stmt C O 
  End :: [Label] -> Val -> Stmt O C

data Val = Z | A | B | C | D | E | X
  deriving (Ord, Show, Eq)

instance NonLocal Stmt where
  entryLabel (Entry l) = l
  successors (End ls _) = ls

prog :: SimpleFuelMonad (FactBase Val)
prog = do
  [entryLabel, l1, l2, l3, l4, l5, l6] <- sequence $ take 7 $ (repeat freshLabel)
  let b0 = mkFirst (Entry entryLabel) <*> mkLast (End [l1] A)
      b1 = mkFirst (Entry l1) <*> mkLast (End [l2, l3, l4] X)
      b2 = mkFirst (Entry l2) <*> mkLast (End [l1] D)
      b3 = mkFirst (Entry l3) <*> mkLast (End [l1] B)
      b4 = mkFirst (Entry l4) <*> mkLast (End [l1] C)
      prog = b0 |*><*| b1 |*><*| b2 |*><*| b3 |*><*| b4
      pass = debugFwdJoins trace (const True) (FwdPass { fp_lattice = lat
                     , fp_transfer = mkFTransfer trans
                     , fp_rewrite = noFwdRewrite })
      lat = DataflowLattice { fact_name = "foo"
                            , fact_bot = Z
                            , fact_join = meet }
      meet _ (OldFact old) (NewFact new) 
        | old == new = (NoChange, new)
        | old < new = (SomeChange, new)
        | otherwise = (NoChange, new)
      trans :: forall e x. Stmt e x -> Val -> Fact x Val
      trans (Entry _) v = v
      trans (End ls v) f = mkFactBase lat (zip ls (repeat v))
      initialFacts = mkFactBase lat (zip [entryLabel, l1, l2, l3, l4, l5, l6] (repeat (fact_bot lat)))
  (_, fb, _) <- analyzeAndRewriteFwd pass (JustC entryLabel) prog initialFacts
  return fb

main = do
  let fb = runSimpleUniqueMonad $ runWithFuel infiniteFuel $ prog
  putStrLn (show fb)
