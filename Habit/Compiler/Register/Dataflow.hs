module Habit.Compiler.Register.Dataflow 
  (optGroups, Optimizer, noOpOpt)

where

import Compiler.Hoopl (Label, runWithFuel, Body, FuelMonad)

import qualified Habit.Compiler.Register.Machine as M (Instr(..), Reg, Label)
import qualified Habit.Compiler.Register.Compiler as C (Group)
import Habit.Compiler.Register.Hoopl (InstrNode, groupsToBody, bodyToGroups)
import qualified Habit.Compiler.Register.NoOp as N (noOpOpt)

type Optimizer = Label -> Body InstrNode -> FuelMonad (Body InstrNode)

-- | Take a list of Machine groups, optimize them all,
-- and return a new list.
optGroups :: Optimizer -> [C.Group] -> [C.Group]
optGroups optimizer groups  = runWithFuel 100 $ do
    (entry, body) <- groupsToBody groups
    body' <- optimizer entry body
    return $ bodyToGroups body'

noOpOpt = N.noOpOpt
