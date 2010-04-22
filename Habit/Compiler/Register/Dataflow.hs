module Habit.Compiler.Register.Dataflow 
  (optGroups, Optimizer, N.noOpOpt, C.constPropOpt, L.liveOpt)

where

import Compiler.Hoopl (Label, runWithFuel, Body, FuelMonad)

import qualified Habit.Compiler.Register.Machine as M (Instr(..), Reg, Label)
import qualified Habit.Compiler.Register.Compiler as C (Group)
import Habit.Compiler.Register.Hoopl (InstrNode, groupsToBody, bodyToGroups)
import qualified Habit.Compiler.Register.NoOp as N (noOpOpt)
import qualified Habit.Compiler.Register.ConstProp as C (constPropOpt)
import qualified Habit.Compiler.Register.Liveness as L (liveOpt)

type Optimizer = Body InstrNode -> FuelMonad (Body InstrNode)

-- | Take a list of Machine groups, optimize them all,
-- and return a new list.
optGroups :: Optimizer -> [C.Group] -> [C.Group]
optGroups optimizer groups  = runWithFuel 100 $ do
    (_, body) <- groupsToBody groups
    body' <- optimizer body
    return $ bodyToGroups body'

