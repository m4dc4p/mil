{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall #-}
module Habit.Compiler.Register.ClosureElimination (cloOpt)

where

import Compiler.Hoopl
import qualified Data.Map as Map

import qualified Habit.Compiler.Register.Machine as H (Reg, Instr(..), Label)
import Habit.Compiler.Register.Hoopl

data CloFact = Return H.Reg H.Label Int | Other
  deriving (Eq, Show)

cloOpt :: Body InstrNode -> FuelMonad (Body InstrNode)
cloOpt body = do
  let bwd = BwdPass { bp_lattice = cloLattice
                       , bp_transfer = cloTransfer 
                       , bp_rewrite = cloRewrite }
  (body', _) <- analyzeAndRewriteBwd bwd body (mkFactBase [])
  return body'

cloLattice :: DataflowLattice CloFact
cloLattice = DataflowLattice { fact_name = "Closure elimination"
                              , fact_bot = Other
                              , fact_extend = extend
                              , fact_do_logging = True }
  where
    extend _ (OldFact old) (NewFact new) 
      | old == new = (NoChange, old)
      | otherwise = (SomeChange, new)
                                           

cloTransfer :: BwdTransfer InstrNode CloFact
cloTransfer (EntryLabel _ _  l) f = mkFactBase [(l, f)]
cloTransfer (LabelNode _ _ l) f = mkFactBase [(l, f)]

cloTransfer (Ret (H.Ret r)) _ = Return r "" 0
cloTransfer (Ret _) _ = error $ "Illegal instruction in Ret found during ClosureElimination."

cloTransfer (Open (H.MkClo r l cnt)) (Return r' _ _)
  | r == r' = Return r l (length cnt)
cloTransfer (Open _) f = f

cloTransfer (Jmp _ _) _ = Other
cloTransfer (FailT _ _ _) _ = Other
cloTransfer (Halt _) _ = Other
cloTransfer (Error _) _ = Other


cloRewrite :: BwdRewrite InstrNode CloFact
cloRewrite = shallowBwdRw rewrite
  where
    rewrite :: SimpleBwdRewrite InstrNode CloFact
    rewrite i@(Open (H.MkClo _ l _)) fact =
      case fact of
        Return _ _ _ -> 
          let note = l ++ ": " ++ show fact 
          in Just $ catGraphs [mkMiddle (Open (H.Note note))
                                         , mkMiddle i]
        Other -> Nothing
    rewrite _ _ = Nothing

