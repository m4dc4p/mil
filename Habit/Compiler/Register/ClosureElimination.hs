{-# LANGUAGE GADTs, NamedFieldPuns, RankNTypes  #-}
{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}
module Habit.Compiler.Register.ClosureElimination (cloOpt)

where

import Compiler.Hoopl
import Data.Maybe (fromMaybe)
import Data.Map (Map, (!))
import qualified Data.Map as Map

import qualified Habit.Compiler.Register.Machine as H (Reg, Instr(..), Label)
import Habit.Compiler.Register.Hoopl
import Habit.Compiler.Register.Liveness (liveOpt)

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

-- | Eliminate useless "Enter" instructions, which only
-- serve to build intermediate closures.
cloOpt :: Body InstrNode -> FuelMonad (Body InstrNode)
cloOpt body = findClosures body >>= uncurry liftClosures >>= liveOpt

liftClosures :: Body InstrNode -> FactBase ProcFact -> FuelMonad (Body InstrNode)
liftClosures body labelFacts = do
  let fwd  = FwdPass { fp_lattice = liftLattice
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
                       CaptureLabel  (G hl) _ _ _ _ l -> (hl, l)
  (body', _) <- analyzeAndRewriteFwd fwd body (mkFactBase initFacts)
  return body'

liftLattice :: DataflowLattice LiftFact
liftLattice = DataflowLattice { fact_bot = Map.empty
                               , fact_name = "Closure elimination."
                               , fact_extend = stdMapJoin extendFact
                               , fact_do_logging = False }
  where
    extendFact :: Label -> OldFact Val -> NewFact Val -> (ChangeFlag, Val)
    extendFact _ (OldFact old) (NewFact new) = (flag, fact)
      where
        fact = if old == new then new else Other
        flag = if fact == old then NoChange else SomeChange

liftTrans :: HLabelMap -> FactBase ProcFact -> FwdTransfer InstrNode LiftFact
liftTrans _ _ (EntryLabel _ _ l) f = fromMaybe Map.empty $ lookupFact f l
liftTrans _ _ (LabelNode _ _ l) f = fromMaybe Map.empty $ lookupFact f l
liftTrans _ _ (CaptureLabel _ _ _ _ _ l) f = fromMaybe Map.empty $ lookupFact f l
liftTrans labelMap labelFacts (Open (H.MkClo dest lab _)) f = 
  case labFact labelFacts (hooplLabel labelMap lab) of
    Proc _ v -> Map.insert dest v f
    _ -> f -- no info known about the label
liftTrans labelMap labelFacts (Open (H.Enter procReg _ resultReg)) f 
    | knownProc procReg = 
        let Clo lab _ = f ! procReg
        -- We know information about the closure in the register. Look up the label 
        -- contained in that closure and assign that information to the result
        -- register here.
        in case labFact labelFacts (hooplLabel labelMap lab) of 
             Proc _ v -> Map.insert resultReg v f
             _ -> f -- no info about the result register
    | otherwise = f -- No info.
  where
    knownProc _ = case fromMaybe Unknown (Map.lookup procReg f) of
       Clo _ _ -> True
       _ -> False
liftTrans _ _ (Open (H.Copy src dst)) fact = Map.insert dst (fromMaybe Unknown $ Map.lookup src fact) fact
liftTrans _ _ (Open (H.Load _ dst)) fact = Map.insert dst Other fact
liftTrans _ _ (Open (H.Set dst _)) fact = Map.insert dst Other fact
liftTrans _ _ (Open _) fact = fact 
liftTrans _ _ (Jmp _ next) fact = mkFactBase [(next, fact)]
liftTrans _ _ (FailT _ (F false) (T true)) fact = mkFactBase [(true, fact)
                                                                      ,(false, fact)]
liftTrans _ _ (Ret _) _ = mkFactBase []
liftTrans _ _ (Halt _) _ = mkFactBase []
liftTrans _ _ (Error _) _ = mkFactBase []
liftTrans _ _ (Capture _ _ _ _) _ = mkFactBase []

hooplLabel :: HLabelMap -> H.Label -> Label
hooplLabel labelMap lab = 
  case Map.lookup lab labelMap of
    Nothing -> error $ "Hardware label " ++ lab ++ " not mapped."
    Just l -> l

labFact :: FactBase ProcFact -> Label -> ProcFact
labFact labelFacts hooplLab = 
  case lookupFact labelFacts hooplLab of
    Nothing -> error $ "No facts about Hoopl label" ++ show hooplLab ++ "."
    Just f -> f

liftRewrite :: FwdRewrite InstrNode LiftFact
liftRewrite = shallowFwdRw rewrite
  where
    rewrite :: SimpleFwdRewrite InstrNode LiftFact
    rewrite (Open (H.Enter target arg resultReg)) facts = 
      case Map.lookup target facts of
        Nothing -> Nothing -- no info
        Just clo -> replaceEnter facts target arg resultReg clo 
    rewrite _ _ = Nothing
    -- A closure being lifted should always have at least one slot, to capture
    -- the argument passed. Still, some optimization may have taken it away
    replaceEnter _ _ _ result (Clo lab 0) = 
      let enter = H.MkClo result lab []
      in Just $ mkMiddle (Open enter)
    replaceEnter _ _ arg result (Clo lab 1) = 
      let enter = H.MkClo result lab [arg]
      in Just $ mkMiddle (Open enter)
    replaceEnter _ target arg result (Clo lab n) = 
      let load i = H.Load (target, i) (target ++ "ce" ++ show i) -- HACK: creating new registers 
                                                                 -- with special prefix again ...
          enter dests = H.MkClo result lab (dests ++ [arg])
          loads = map load [0..n-2]
          newRegs = map (\(H.Load _ r) -> r) loads
          instrs = loads ++ [enter newRegs]
      in Just $ catGraphs (map (mkMiddle . Open) instrs)
    replaceEnter _ _ _ _ _ = Nothing

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
findCloTrans (CaptureLabel _ _ _ _ _ l) f = mkFactBase [(l, f)]
-- Capture indicates this group captures a closure.
findCloTrans (Capture r (N l) _ cnt) _ = Proc r (Clo l cnt)
-- Any other closed instruction tells us the group
-- does not capture a closure.
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
findCloTrans (Open _) f = f

findCloRewrite :: InstrNode e x -> Fact x ProcFact -> Maybe (BwdRes InstrNode ProcFact e x)
findCloRewrite = shallowBwdRw f
  where
    f :: SimpleBwdRewrite InstrNode ProcFact
    f i@(EntryLabel _ _ _) procFact = Just $ mkFirst i <*> mkNote (show procFact)
    f i@(LabelNode _ _ _) procFact = Just $ mkFirst i <*> mkNote (show procFact)
    f _ _ = Nothing

mkNote :: String -> AGraph InstrNode O O
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
