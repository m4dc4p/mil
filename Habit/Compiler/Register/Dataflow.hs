{-# LANGUAGE GADTs #-}
module Habit.Compiler.Register.Dataflow (makeGraph)

where

import Compiler.Hoopl
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Habit.Compiler.Register.Machine as M (Instr(..), Reg, Label)
import qualified Habit.Compiler.Register.Compiler as C

data InstrNode e x where
  LabelNode :: M.Instr -- ^ Original instruction
            -> Label -- ^ Numeric label
            -> InstrNode C O
  Enter :: M.Instr -- ^ Original instruction
        -> InstrNode O O
  Copy :: M.Instr -- ^ Original instruction
       -> InstrNode O O
  Ret :: M.Instr -- ^ Original instruction
         -> InstrNode O C
  Rest :: M.Instr -- ^ Original instruction
       -> InstrNode O O

instance Edges InstrNode where
  entryLabel (LabelNode _ l) = l
  successors (Ret _) = []

data HasConst = Top | R M.Label
  deriving Eq 

type ConstFact = Map.Map M.Reg HasConst

-- | Turn a group into a body.  Probably need
-- to maintain map of Machine labels to Hoopl labels,
-- or use a hash function to turn Machine labels
-- into Hoopl lables.
makeBody :: C.Group -> FuelMonad (Body InstrNode)
makeBody (_, _, blocks) = do
      -- Turn a list of blocks into a body.
  let toBody :: [Block InstrNode O C] -> Body InstrNode
      toBody = undefined

      -- Turn a list of instructions into a block.
      toBlock :: (C.Label, [M.Instr]) -> FuelMonad (Block InstrNode O C)
      toBlock (lab, instrs) = do
        let firstInstr = LabelNode (M.Label lab) (hash l)
        return . foldl BCat firstInstr . map (BUnit . mkBlock) $ instrs

      -- Turn a (string) label into a numeric label
      hash :: String -> Label
      hash = undefined

      -- Turn a machine instruction into a InstrNode
      mkNode instr@(M.Label l) = LabelNode instr (hash l)
      mkNode instr@(M.Enter _ _ _) = Enter instr
      mkNode instr@(M.Copy _ _) = Copy instr
      mkNode instr@(M.Ret _) = Ret instr
      mkNode instr = Rest instr
  mapM toBlock blocks >>= return . toBody

-- | Apply constant propogation to a body.
optBody :: Body InstrNode -> FuelMonad (Body InstrNode)
optBody body = do
  let fwd  = FwdPass { fp_lattice = constLattice
                     , fp_transfer = varHasConst
                     , fp_rewrite = constProp }
      -- Initial map of registers to values in
      -- the body
      initFact = undefined
      -- The entry point for the body
      entry :: Label 
      entry = undefined
  (body', _) <- analyzeAndRewriteFwd fwd body (mkFactBase [(entry, initFact body)])
  return body'

-- | Turn a body back into a Group of Machine instructions. How
-- to recover labels?  
bodyToGroup :: Body InstrNode -> C.Group
bodyToGroup = undefined

-- | Take a list of Machine groups, optimize them all,
-- and return a new list.
makeGraph :: [C.Group] -> FuelMonad [C.Group]
makeGraph groups = 
  mapM makeBody groups >>= 
       mapM optBody >>=  
            return . map bodyToGroup

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
    --   * All entries are equal. Return (NoChange, updated map)
    --   * Facts have been taken away. Return (SomeChange, updated map)
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

constProp = undefined

  