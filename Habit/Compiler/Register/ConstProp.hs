module Habit.Compiler.Register.ConstProp

where

import Compiler.Hoopl
import Data.Map (Map)
import qualified Data.Map as Map

data HasConst = Top | R M.Label
  deriving Eq 

type ConstFact = Map.Map M.Reg HasConst

constLattice :: DataflowLattice ConstFact
constLattice = DataflowLattice { fact_bot = Map.empty
                               , fact_name = "Constant propagation"
                               , fact_extend = extendFacts
                               , fact_do_logging = False }
  where
    extendFacts :: (OldFact ConstFact) -> (NewFact ConstFact) -> (ChangeFlag, ConstFact)
    -- Determine if new constants change old facts. A couple of cases 
    -- to consider. 
    --   * New entries are present. Return (SomeChange, updated map)
    --   * Some entries are not equal. Return (SomeChange, updated map)
    --   * Facts have been taken away. Return (SomeChange, updated map)
    --   * All entries are equal. Return (NoChange, updated map)
    extendFacts (OldFact old) (NewFact new) = 
      let updateCommon :: M.Reg -> HasConst -> HasConst -> (Bool, HasConst)
          updateCommon _ o n 
            | o == n = (False, n)
            | otherwise = (True, Top)
          -- common elements with change attached
          commonB :: Map M.Reg (Bool, HasConst)
          commonB = Map.intersectionWithKey updateCommon new old
          -- common elements with HasConst only
          common :: Map M.Reg HasConst
          common = Map.map snd commonB

          onlyOld :: Map M.Reg HasConst
          onlyOld = Map.difference old common
          onlyNew :: Map M.Reg HasConst
          onlyNew = Map.difference new common

          commonChanged = or . map fst . Map.elems $ commonB
          elemAdded = not (Map.null onlyNew)
          elemRemoved = not (Map.null onlyOld)

          newMap' = Map.union onlyNew common
      in if elemAdded || elemRemoved || commonChanged
         then (SomeChange, newMap')
         else (NoChange, new)

varHasConst :: FwdTransfer InstrNode ConstFact
varHasConst (LabelNode i instr) = undefined
varHasConst (Enter instrS) = undefined
varHasConst (Copy instr) = undefined
varHasConst (Rest instr) = undefined

constProp :: FwdTransfer InstrNode ConstFact
constProp = undefined
