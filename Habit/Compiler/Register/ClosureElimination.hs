{-# LANGUAGE GADTs, NamedFieldPuns, RankNTypes  #-}
{-# OPTIONS_GHC -Wall #-}
module Habit.Compiler.Register.ClosureElimination (cloOpt)

where

import Compiler.Hoopl
import Data.Maybe (fromMaybe)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap

import qualified Habit.Compiler.Register.Machine as H (Reg, Instr(..), Label)
import Habit.Compiler.Register.Hoopl

-- | Values that can be returned from a procedure. 
data Val = Unknown -- ^ No information about the value returned.
         | Other -- ^ A value that is not a closure is returned.
         | Clo H.Label Int -- ^ A closure pointing at the label
                           -- specified with the given number of slots
                           -- is returned.
  deriving (Eq, Show)

-- | Indicates if a procedure returns a closure
-- or something else.
data ProcFact = Proc H.Reg Val | NoInfo
  deriving (Eq, Show)

-- | The values held by a register. 
type LiftFact = Map H.Reg Val

-- | Maps Machine (i.e., "hardware") labels to Hoopl labels.
type HLabelMap = Map H.Label Label

cloOpt :: Body InstrNode -> FuelMonad (Body InstrNode)
cloOpt body = do
  (body', facts) <- findClosures body
  liftClosures body' facts 

liftClosures :: Body InstrNode -> FactBase ProcFact -> FuelMonad (Body InstrNode)
liftClosures body labelFacts = do
  let fwd  = FwdPass { fp_lattice = undefined -- liftLattice 
                     , fp_transfer = liftTrans labelMap labelFacts
                     , fp_rewrite = liftRewrite }
      -- Initial map of labels to initial facts.
      bodies = bodyList body
      initFacts = zip (map fst bodies) (repeat Map.empty)
      labelMap = Map.fromList (map (labels . snd) bodies)
      labels :: Block InstrNode C C -> (H.Label, Label)
      labels block = case blockLabel block of
                       EntryLabel (G hl) _ l -> (hl, l)
                       LabelNode  _ (N hl) l -> (hl, l)
  (body', _) <- analyzeAndRewriteFwd fwd body (mkFactBase initFacts)
  return body'

liftTrans :: HLabelMap -> FactBase ProcFact -> FwdTransfer InstrNode LiftFact
liftTrans _ labelFacts (EntryLabel _ _ l) f = fromMaybe Map.empty $ lookupFact f l
liftTrans _ labelFacts (LabelNode _ _ l) f = fromMaybe Map.empty $ lookupFact f l
liftTrans labelMap labelFacts (Open (H.MkClo dest lab regs)) f = Map.insert dest (Clo lab (length regs)) f
liftTrans labelMap labelFacts (Open (H.Enter procReg _ resultReg)) f 
    | knownProc procReg = 
        let Clo lab cnt = f ! procReg
            hooplLab = fromMaybe (error $ "Hardware label " ++ lab ++ " not mapped.") (Map.lookup lab labelMap)
            labFact = fromMaybe (error $ "No facts about Hoopl label" ++ show hooplLab ++ ".") (lookupFact labelFacts hooplLab)
        -- We know information about the closure in the register. Look up the label 
        -- contained in that closure and assign that information to the result
        -- register here.
        in case labFact of 
             Proc _ v -> Map.insert resultReg v f
             _ -> f -- no info about the result register
    | otherwise = f -- No info.
  where
    knownProc r = case fromMaybe Unknown (Map.lookup procReg f) of
       Clo lab cnt -> True
       _ -> False
{- liftTrans _ _ (Open (H.Copy src dst)) fact = Map.insert dst (R src) fact
liftTrans _ _ (Open (H.Load _ dst)) fact = Map.insert dst Top fact
liftTrans _ _ (Open (H.Set dst _)) fact = Map.insert dst Top fact
liftTrans _ _ (Open _) fact = fact -}
liftTrans _ labelFacts (Jmp _ next) fact = mkFactBase [(next, fact)]
liftTrans _ labelFacts (FailT _ (F false) (T true)) fact = mkFactBase [(true, fact)
                                                                      ,(false, fact)]
liftTrans _ _ (Ret _) fact = mkFactBase []
liftTrans _ _ (Halt _) fact = mkFactBase []
liftTrans _ _ (Error _) fact = mkFactBase []

liftRewrite :: FwdRewrite InstrNode LiftFact
liftRewrite = shallowFwdRw rewrite
  where
    rewrite :: SimpleFwdRewrite InstrNode LiftFact
    rewrite i@(Open (H.Enter dest arg resultReg)) facts = 
      case Map.lookup dest facts of
        Nothing -> Nothing -- no info
        Just (Clo lab cnt) -> Just $ mkNote ("Closure contains " ++ show lab ++ " and takes " ++ show cnt ++ " arguments.") <*>
                                 mkMiddle i
    rewrite _ _ = Nothing

findClosures :: Body InstrNode -> FuelMonad (Body InstrNode, FactBase ProcFact)
findClosures body = do
  let bwd = BwdPass { bp_lattice = findCloLat
                    , bp_transfer = findCloTrans
                    , bp_rewrite = findCloRewrite }
  analyzeAndRewriteBwd bwd body (mkFactBase [])

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

findCloRewrite :: InstrNode e x -> Fact x ProcFact -> Maybe (BwdRes InstrNode ProcFact e x)
findCloRewrite = shallowBwdRw f
  where
    f :: SimpleBwdRewrite InstrNode ProcFact
    f i@(EntryLabel _ _ l) procFact = Just $ mkFirst i <*> mkNote (show procFact)
    f i@(LabelNode _ _ l) procFact = Just $ mkFirst i <*> mkNote (show procFact)
    f _ _ = Nothing

mkNote = mkMiddle . Open . H.Note

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
