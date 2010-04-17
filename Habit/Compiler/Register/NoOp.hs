{-# LANGUAGE GADTs #-}
module Habit.Compiler.Register.NoOp (noOpOpt)

where

import Compiler.Hoopl
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Habit.Compiler.Register.Machine as M (Reg)
import Habit.Compiler.Register.Hoopl

-- | Apply constant propogation to a body.
noOpOpt :: Label -> Body InstrNode -> FuelMonad (Body InstrNode)
noOpOpt entry body = do
  let fwd  = FwdPass { fp_lattice = noOpLattice -- constLattice
                     , fp_transfer = noOpTransfer -- varHasConst
                     , fp_rewrite = noOpProp {- constProp  -} }
      -- Initial map of registers to values in
      -- the body
      initFacts = zip (map fst (bodyList body)) (repeat Map.empty)
  (body', _) <- analyzeAndRewriteFwd fwd body (mkFactBase initFacts)
  return body'

data NoOp = NoOp
  deriving Eq 

type NoOpFact = Map M.Reg NoOp

noOpLattice :: DataflowLattice NoOpFact
noOpLattice = DataflowLattice { fact_bot = Map.empty
                               , fact_name = "Constant propagation"
                               , fact_extend = noOpExtend
                               , fact_do_logging = False }

-- type FwdTransfer n f 
-- forall e x. n e x -> Fact e f -> Fact x f 
noOpTransfer :: FwdTransfer InstrNode NoOpFact
noOpTransfer (LabelNode _ l) f = Map.empty
noOpTransfer (Rest _) f = f
noOpTransfer (Enter _ _) f = mkFactBase []
noOpTransfer (Ret _) f = mkFactBase []
noOpTransfer (Halt _) f = mkFactBase []
noOpTransfer (FailT _ _ _) f = mkFactBase []
noOpTransfer (Jmp _ _) f = mkFactBase []
noOpTransfer (Error _) f = mkFactBase []

noOpProp :: FwdRewrite InstrNode NoOpFact
noOpProp = noFwdRewrite

noOpExtend (OldFact f) _ = (NoChange, f)
