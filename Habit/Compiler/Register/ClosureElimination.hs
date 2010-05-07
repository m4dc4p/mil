{-# LANGUAGE GADTs, NamedFieldPuns, RankNTypes  #-}
{-# OPTIONS_GHC -Wall #-}
module Habit.Compiler.Register.ClosureElimination (cloOpt)

where

import Compiler.Hoopl
import Data.Maybe (fromMaybe)

import qualified Habit.Compiler.Register.Machine as H (Reg, Instr(..), Label)
import Habit.Compiler.Register.Hoopl

data Val = Unknown | Other | Clo H.Label Int
  deriving (Eq, Show)

-- | Indicates if a procedure returns a closure
-- or something else.
data ProcFact = Proc H.Reg Val | NoInfo
  deriving (Eq, Show)

cloOpt :: Body InstrNode -> FuelMonad (Body InstrNode)
cloOpt body = return body

findClosures :: Body InstrNode -> FuelMonad (FactBase ProcFact)
findClosures body = do
  let bwd = BwdPass { bp_lattice = findCloLat
                    , bp_transfer = findCloTrans
                    , bp_rewrite = findCloRewrite }
  analyzeAndRewriteBwd bwd body (mkFactBase []) >>= return . snd

findCloLat :: DataflowLattice ProcFact
findCloLat = DataflowLattice { fact_bot = NoInfo
                             , fact_name = "Find procedures that return closures."
                             , fact_extend = extendFact
                             , fact_do_logging = False }
  where
    extendFact :: Label -> OldFact ProcFact -> NewFact ProcFact -> (ChangeFlag, ProcFact)
    extendFact _ (OldFact old) (NewFact new) = 
      let p = procMeet old new
      in (if p == new then NoChange else SomeChange
         , p)


findCloTrans :: BwdTransfer InstrNode ProcFact
-- Return what we've found out so far.
findCloTrans (EntryLabel _ _ l) f = mkFactBase [(l, f)]
findCloTrans (LabelNode _ _  l) f = mkFactBase [(l, f)]
-- Finding a return instruction lets us know what 
-- register is returned from this procedure. Next
-- need to figure out what value it can hold
findCloTrans (Ret r) _ = Proc r Unknown
-- Combine facts from both branches to determine
-- if our return register remains unchanged.
findCloTrans (FailT _ (F fl) (T tl)) f =
  let fp = fromMaybe NoInfo $ lookupFact f fl
      tp = fromMaybe NoInfo $ lookupFact f tl
  in procMeet tp fp
-- Transfer facts known so far from destination label
findCloTrans (Jmp _ l) f = fromMaybe NoInfo $ lookupFact f l
-- Nothing known yet in these cases.
findCloTrans (Halt _) _ = NoInfo
findCloTrans (Error _) _ = NoInfo
-- Determine if this MkClo instruction affects our destination
-- register and, if so, if that overrides information already
-- known or tells us that the procedure returns a closure.
findCloTrans (Open (H.MkClo dest lab regs)) f@(Proc r _)  
  | dest == r = procMeet f (Proc dest (Clo lab (length regs)))
findCloTrans (Open (H.Enter _ _ dest)) (Proc r _) 
  | dest == r = Proc r Other
findCloTrans (Open (H.AllocD dest _ _)) (Proc r _) 
  | dest == r = Proc r Other
findCloTrans (Open (H.Copy _ dest)) (Proc r _) 
  | dest == r = Proc r Other
findCloTrans (Open (H.Load _ dest)) (Proc r _)
  | dest == r = Proc r Other
findCloTrans (Open (H.Set dest _)) (Proc r _) 
  | dest == r = Proc r Other
findCloTrans (Open _) f = f

findCloRewrite :: forall n e x f. n e x -> Fact x f -> Maybe (BwdRes n f e x)
findCloRewrite = noBwdRewrite

-- | Combines Proc values such that 
-- any ambiguity in the value held by the register
-- results in a ``bottom'' (i.e., @Other@) value.
procMeet :: ProcFact -> ProcFact -> ProcFact
procMeet (Proc r v) (Proc r' v') 
  | r == r' = if v == v'
              then Proc r v
              else case (v, v') of
                     (Unknown, _) -> Proc r v'
                     (_, Unknown) -> Proc r v
                     (Other, _) -> Proc r Other
                     (_, Other) -> Proc r Other
                     _ -> Proc r Other
  | otherwise = error $ "procMeet: return registers should not differ: " ++ show (r, r')
procMeet p p' = if p == NoInfo
                then p'
                else p
