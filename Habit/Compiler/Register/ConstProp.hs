{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall #-}
module Habit.Compiler.Register.ConstProp 
  (constPropOpt, ConstFact, HasConst(..))

where

import Compiler.Hoopl hiding (Top)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

import qualified Habit.Compiler.Register.Machine as H (Reg, Instr(..))
import Habit.Compiler.Register.Hoopl

-- | Indicates if a register holds a constant value or if it
-- gets overwritten. The key for the map is the *destination*
-- register. 
type ConstFact = Map H.Reg HasConst

-- | Indicates the value held by a register.
data HasConst = Top -- ^ The register holds an unknown value.
              | R H.Reg -- ^ The register holds a copy of another register
              | Fields [H.Reg] -- ^ The register holds a data value with
                          -- fields that are copies of the given
                          -- registers.
  deriving (Eq, Show)


constPropOpt :: Body InstrNode -> FuelMonad (Body InstrNode)
constPropOpt body = constProp body >>= return . fst

constProp :: Body InstrNode -> FuelMonad (Body InstrNode, FactBase ConstFact)
constProp body = do
  let fwd  = FwdPass { fp_lattice = constLattice
                     , fp_transfer = constTransfer
                     , fp_rewrite = constRewrite }
      -- Initial map of labels to initial facts.
      initFacts = zip (map fst (bodyList body)) (repeat Map.empty)
  analyzeAndRewriteFwd fwd body (mkFactBase initFacts)


constLattice :: DataflowLattice ConstFact
constLattice = DataflowLattice { fact_bot = Map.empty
                               , fact_name = "Constant propagation"
                               , fact_extend = stdMapJoin extendFact
                               , fact_do_logging = False }
  where
    extendFact :: Label -> OldFact HasConst -> NewFact HasConst -> (ChangeFlag, HasConst)
    extendFact _ (OldFact old) (NewFact new) = (flag, fact)
      where
        fact = if old == new then new else Top
        flag = if fact == old then NoChange else SomeChange
        
constTransfer :: FwdTransfer InstrNode ConstFact
constTransfer (EntryLabel _ _ l) f = fromMaybe Map.empty $ lookupFact f l
constTransfer (LabelNode _ _ l) f = fromMaybe Map.empty $ lookupFact f l
constTransfer (CaptureLabel _ _ _ _ _ l) f = fromMaybe Map.empty $ lookupFact f l
constTransfer (Open (H.MkClo dst _ srcs)) fact 
            | null srcs = fact
            | otherwise = Map.insert dst (Fields srcs) fact
constTransfer (Open (H.Copy src dst)) fact = Map.insert dst (R src) fact
constTransfer (Open (H.Load _ dst)) fact = Map.insert dst Top fact
constTransfer (Open (H.Set dst _)) fact = Map.insert dst Top fact
constTransfer (Open (H.Enter _ _ dst)) fact = Map.insert dst Top fact
constTransfer (Open _) fact = fact
constTransfer (Jmp _ next) fact = mkFactBase [(next, fact)]
constTransfer (FailT _ (F false) (T true)) fact = mkFactBase [(true, fact)
                                                   ,(false, fact)]
constTransfer (Ret _) _ = mkFactBase []
constTransfer (Capture _ _ _ _) _ = mkFactBase []
constTransfer (Halt _) _ = mkFactBase []
constTransfer (Error _) _ = mkFactBase []

-- Takes a node and facts. Returns a Maybe Graph
-- forall e x. n e x -> Fact e f -> Fact x f 
-- forall e x. InstrNode e x -> Fact e ConstFact -> Fact x f ConstFact
constRewrite :: FwdRewrite InstrNode ConstFact
constRewrite = shallowFwdRw rewrite
  where
    rewrite :: InstrNode e x -> Fact e ConstFact -> Maybe (AGraph InstrNode e x)
    rewrite (Ret r) facts = case findConst r facts of
                                      Just s -> Just $ mkLast (Ret s)
                                      Nothing -> Nothing
    rewrite _ _ = Nothing
    findConst r facts = case Map.lookup r facts of
                          Just (R s) -> Just s
                          _ -> Nothing


