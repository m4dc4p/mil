{-# LANGUAGE GADTs #-}
module Habit.Compiler.Register.Dataflow (makeGraph)

where

import Data.Char (ord)
import Compiler.Hoopl
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Habit.Compiler.Register.Machine as M (Instr(..), Reg, Label)
import qualified Habit.Compiler.Register.Compiler as C
import Habit.Compiler.Register.Hoopl

-- | Take a list of Machine groups, optimize them all,
-- and return a new list.
makeGraph :: [C.Group] -> (Int, Int, [C.Group])
makeGraph groups = runWithFuel 100 $ do
    (entry, body) <- makeBody undefined
    body' <- optBody entry body
    return $ (length (bodyList body), length (bodyList body'), bodyToGroup body')
  where
    -- | Turn a body back into a Group of Machine instructions. 
    bodyToGroup :: Body InstrNode -> [C.Group]
    bodyToGroup = map toGroup . bodyList
    toGroup :: (Label, Block InstrNode e x) -> C.Group
    toGroup (_, block) = 
      let instrs = toCode block
      in ("", 0, [("", instrs)])
    toCode :: Block InstrNode e x -> [M.Instr]
    toCode (BUnit i) = [toInstr i]
    toCode (b1 `BCat` b2) = toCode b1 ++ toCode b2
    toInstr :: InstrNode e x -> M.Instr
    toInstr (LabelNode i l) = i
    toInstr (Enter i) = i
    toInstr (Copy i) = i
    toInstr (Ret i) = i
    toInstr (Halt i) = i 
    toInstr (Rest i) = i

-- | Apply constant propogation to a body.
optBody :: Label -> Body InstrNode -> FuelMonad (Body InstrNode)
optBody entry body = do
  let fwd  = FwdPass { fp_lattice = noOpLattice -- constLattice
                     , fp_transfer = noOpTransfer -- varHasConst
                     , fp_rewrite = noOpProp -- constProp 
                     }
      -- Initial map of registers to values in
      -- the body
      initFact _ = Map.empty
  (body', _) <- analyzeAndRewriteFwd fwd body (mkFactBase [(entry, initFact body)])
  return body'

data NoOp = NoOp
  deriving Eq 

type NoOpFact = Map.Map M.Reg NoOp

noOpLattice :: DataflowLattice NoOpFact
noOpLattice = DataflowLattice { fact_bot = Map.empty
                               , fact_name = "Constant propagation"
                               , fact_extend = noOpExtend
                               , fact_do_logging = False }

-- type FwdTransfer n f 
-- forall e x. n e x -> Fact e f -> Fact x f 
noOpTransfer :: FwdTransfer InstrNode NoOpFact
noOpTransfer (LabelNode _ l) f = Map.empty
noOpTransfer (Enter _) f = f
noOpTransfer (Copy _) f = f
noOpTransfer (Rest _) f = f
noOpTransfer (Ret _) f = mkFactBase []
noOpTransfer (Halt _) f = mkFactBase []

noOpProp :: FwdRewrite InstrNode NoOpFact
noOpProp = noFwdRewrite

noOpExtend (OldFact f) _ = (NoChange, f)


