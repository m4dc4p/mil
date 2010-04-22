{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall #-}
module Habit.Compiler.Register.Liveness

where

import Compiler.Hoopl
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Habit.Compiler.Register.Machine as M (Reg, Instr(..))
import Habit.Compiler.Register.Hoopl

type LiveFact = Set M.Reg

liveOpt :: Body InstrNode -> FuelMonad (Body InstrNode)
liveOpt body = do
  let bwd = BwdPass { bp_lattice = liveLattice
                       , bp_transfer = liveTransfer 
                       , bp_rewrite = liveRewrite }
      initFacts = zip (map fst (bodyList body)) (repeat Set.empty)
  (body', _) <- analyzeAndRewriteBwd bwd body (mkFactBase initFacts)
  return body'

liveLattice :: DataflowLattice LiveFact
liveLattice = DataflowLattice { fact_name = "Liveness"
                              , fact_bot = Set.empty
                              , fact_extend = undefined -- stdMapJoin extendLive
                              , fact_do_logging = True }

{- | liveTransfer adds facts based on the type of node:

    Open/Closed: Transfer all live registers from target labels.
    Open/Open: Transfer all register that are live, remove any that are killed.
    Closed/Open: Return all registers that are known to be live now.
-}
liveTransfer :: BwdTransfer InstrNode LiveFact
liveTransfer (EntryLabel _ _ l) f = mkFactBase [(l, f)]
liveTransfer (LabelNode _ _ l) f = mkFactBase [(l, f)]
liveTransfer (Open (M.Enter _ _ dest)) f = Set.delete dest f
liveTransfer (Open (M.AllocC dest _ _)) f = Set.delete dest f
liveTransfer (Open (M.AllocD dest _ _)) f = Set.delete dest f
liveTransfer (Open (M.Copy _ dest)) f = Set.delete dest f
liveTransfer (Open (M.Store src (dest, _))) f = Set.insert src (Set.delete dest f)
liveTransfer (Open (M.Load (dest,_) src)) f = Set.insert src (Set.delete dest f)
liveTransfer (Open (M.Set dest _)) f = Set.delete dest f
liveTransfer (Open _) f = f
liveTransfer (Closed _ l) f = fromMaybe Set.empty $ lookupFact f l
liveTransfer (FailT _ tl fl) f = fromMaybe Set.empty (lookupFact f tl) `Set.union`
                                               fromMaybe Set.empty (lookupFact f fl)
liveTransfer (Ret _) _ = Set.empty
liveTransfer (Error _) _ = Set.empty
liveTransfer (Halt _) _ = Set.empty

-- type BwdRewrite n f = forall e x. n e x -> Fact x f -> Maybe (BwdRes n f e x)
-- data BwdRes n f e x = BwdRes (AGraph n e x) (BwdRewrite n f)
liveRewrite :: BwdRewrite InstrNode LiveFact
liveRewrite = undefined
                                               