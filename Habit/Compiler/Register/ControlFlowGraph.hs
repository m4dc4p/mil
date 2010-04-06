module Habit.Compiler.Register.ControlFlowGraph (makeCFG, writeViz)

where

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Tree
import Data.Graph.Inductive.Graphviz
import System.IO

import Habit.Compiler.Register.Compiler
import Habit.Compiler.Register.Machine

makeCFG :: [Group] -> Gr String ()
makeCFG groups = 
    let emptyAdj = [] :: [((), Node)] -- empty adjacency list
        adj p = [((), p)] -- single adjacent node
        addInstr :: (Gr String (), (Int, Int)) -> Instr -> (Gr String (), (Int, Int))
        addInstr s (Note _) = s
        addInstr (g, (prev, next)) instr = ((adj prev
                                     , next
                                     , showInstr instr
                                     , emptyAdj) & g, (next, next + 1))
        addLabel :: (Gr String (), Int) -> Code -> (Gr String (), Int)
        addLabel (g, m) (label, instrs) = 
          let labNode = (emptyAdj
                        , m
                        , label
                        , emptyAdj)
              (instrGraph, (_, m')) = foldl addInstr (labNode & g, (m, m + 1)) instrs
          in (instrGraph, m')
        mkSubGraph :: (Gr String (), (Maybe Int, Int)) -> Group -> (Gr String (), (Maybe Int, Int))
        mkSubGraph (g, (prev, n)) (_, _, blocks) = 
          let (subgraph, n') = foldl addLabel (g, n) blocks
          in (subgraph, (Just n', n' + 1))
    in fst $ foldl mkSubGraph (empty, (Nothing, 0)) groups

showInstr :: Instr -> String
showInstr (Enter _ _ _) = "Enter"
showInstr (Ret _) = "Ret"
showInstr (AllocC _ _ _) = "AllocC"
showInstr (AllocD _ _ _) = "AllocD"
showInstr (Copy _ _) = "Copy"
showInstr (Store _ _) = "Store"
showInstr (Load _ _) = "Load"
showInstr (Set _ _) = "Set"
showInstr (FailT _ _ _) = "FailT"
showInstr (Label _) = "Label"
showInstr (Halt) = "Halt"
showInstr (Jmp _) = "Jmp"
showInstr (Error _) = "Error"
showInstr (Note _) = "Note"

writeViz file gr = do
  let viz = graphviz' gr
  withFile (file ++ ".dot") WriteMode (\h -> hPutStr h viz)
        
