module Habit.Compiler.Register.ControlFlowGraph (makeCFG)

where

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Tree
import Habit.Compiler.Register.Compiler
import Habit.Compiler.Register.Machine

makeCFG :: [Group] -> Gr Instr ()
makeCFG = undefined

