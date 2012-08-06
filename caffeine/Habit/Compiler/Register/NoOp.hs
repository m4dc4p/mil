{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}
module Habit.Compiler.Register.NoOp (noOpOpt)

where

import Compiler.Hoopl
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Habit.Compiler.Register.Machine as H (Reg)
import Habit.Compiler.Register.Hoopl

-- | Apply constant propogation to a body.
noOpOpt :: Body InstrNode -> FuelMonad (Body InstrNode)
noOpOpt body = do
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

type NoOpFact = Map H.Reg NoOp

noOpLattice :: DataflowLattice NoOpFact
noOpLattice = DataflowLattice { fact_bot = Map.empty
                               , fact_name = "Constant propagation"
                               , fact_extend = noOpExtend
                               , fact_do_logging = False }

-- type FwdTransfer n f 
-- forall e x. n e x -> Fact e f -> Fact x f 
noOpTransfer :: FwdTransfer InstrNode NoOpFact
noOpTransfer (LabelNode _ _ _) _ = Map.empty
noOpTransfer (EntryLabel _ _ _) _ = Map.empty
noOpTransfer (CaptureLabel _ _ _ _ _ _) _ = Map.empty
noOpTransfer (Open _) f = f
noOpTransfer (Jmp _ _) _ = mkFactBase []
noOpTransfer (Ret _) _ = mkFactBase []
noOpTransfer (Capture _ _ _ _) _ = mkFactBase []
noOpTransfer (Halt _) _ = mkFactBase []
noOpTransfer (FailT _ _ _) _ = mkFactBase []
noOpTransfer (Error _) _ = mkFactBase []

noOpProp :: FwdRewrite InstrNode NoOpFact
noOpProp = noFwdRewrite

noOpExtend :: t -> OldFact t1 -> t2 -> (ChangeFlag, t1)
noOpExtend _ (OldFact f) _ = (NoChange, f)
