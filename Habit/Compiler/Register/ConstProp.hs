{-# LANGUAGE GADTs #-}
module Habit.Compiler.Register.ConstProp (constPropOpt)

where

import Compiler.Hoopl hiding (Top)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

import qualified Habit.Compiler.Register.Machine as M (Reg, Label, Instr(..))
import Habit.Compiler.Register.Hoopl

data HasConst = Top | R M.Reg
  deriving Eq 

-- Indicates if a register holds a constant value or if it
-- gets overwritten. The key for the map is the *destination*
-- register. 
type ConstFact = Map M.Reg HasConst

constPropOpt :: Body InstrNode -> FuelMonad (Body InstrNode)
constPropOpt body = do
  let fwd  = FwdPass { fp_lattice = constLattice
                     , fp_transfer = varHasConst
                     , fp_rewrite = constProp }
      -- Initial map of labels to initial facts.
      initFacts = zip (map fst (bodyList body)) (repeat Map.empty)
  (body', _) <- analyzeAndRewriteFwd fwd body (mkFactBase initFacts)
  return body'


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
        
varHasConst :: FwdTransfer InstrNode ConstFact
varHasConst (EntryLabel _ _ l) f = fromMaybe Map.empty $ lookupFact f l
varHasConst (LabelNode _ _ l) f = fromMaybe Map.empty $ lookupFact f l
varHasConst (Open (M.Copy src dst)) fact = Map.insert dst (R src) fact
varHasConst (Open (M.Load _ dst)) fact = Map.insert dst Top fact
varHasConst (Open (M.Set dst _)) fact = Map.insert dst Top fact
varHasConst (Open _) fact = fact
varHasConst (Closed _ next) fact = mkFactBase [(next, fact)]
varHasConst (FailT _ (F false) (T true)) fact = mkFactBase [(true, fact)
                                                   ,(false, fact)]
varHasConst (Ret _) fact = mkFactBase []
varHasConst (Halt _) fact = mkFactBase []
varHasConst (Error _) fact = mkFactBase []

-- Takes a node and facts. Returns a Maybe Graph
-- forall e x. n e x -> Fact e f -> Fact x f 
-- forall e x. InstrNode e x -> Fact e ConstFact -> Fact x f ConstFact
constProp :: FwdRewrite InstrNode ConstFact
constProp = shallowFwdRw rewrite
  where
    rewrite :: InstrNode e x -> Fact e ConstFact -> Maybe (AGraph InstrNode e x)
    rewrite (Ret (M.Ret r)) facts = case findConst r facts of
                                      Just s -> Just $ mkLast (Ret (M.Ret s))
                                      Nothing -> Nothing
    rewrite n facts = Nothing
    findConst r facts = case Map.lookup r facts of
                          Just (R s) -> Just s
                          _ -> Nothing


