{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}
module Habit.Compiler.Register.ControlFlowGraph (makeCFG, writeViz)

where

import System.IO
import Data.Graph.Inductive.Graph ((&), Node)
import qualified Data.Graph.Inductive.Graph as G (empty)
import Data.Graph.Inductive.Tree (Gr)
import Data.Graph.Inductive.Graphviz (graphviz')
import Data.Map (Map, (!))
import qualified Data.Map as Map

import Habit.Compiler.Register.Compiler (Group, Code, Label, Target(..))
import qualified Habit.Compiler.Register.Compiler as C (Group(..))
import Habit.Compiler.Register.Machine (Instr(..), Failure(..), Success(..))
import qualified Habit.Compiler.Register.Machine as H (Instr(..))

makeCFG :: [Group] -> Gr String ()
makeCFG groups = 
    let emptyAdj = [] :: [((), Node)] -- empty adjacency list
        adj :: Node -> [((), Node)]
        adj p = adjs [p] -- single adjacent node
        adjs ps = map (\p -> ((), p)) ps -- many adjacent nodes
        -- add a node with forward links
        forward node prevNode succNodes instr = (adj prevNode
                                               , node
                                               , showInstr instr
                                               , adjs succNodes)
        -- Add control links between instructions and labels
        linkInstr :: Map Label Node -> (Gr String (), (Node, Int)) -> Instr -> (Gr String (), (Node, Int))
        linkInstr labelMap (g, (prev, next)) instr@(Jmp label) 
          = (forward next prev [(labelMap ! label)] instr & g, (next, next + 1))
        linkInstr labelMap (g, (prev, next)) instr@(FailT _ _ (F fail) (S success)) 
          = ((adj prev
             , next
             , showInstr instr
             , adjs [(labelMap ! fail)
                    , (labelMap ! success)]) & g, (next, next + 1))
        linkInstr _ s (Note _) = s
        linkInstr _ (g, (prev, next)) instr 
          = ((adj prev
             , next
             , showInstr instr
             , emptyAdj) & g, (next, next + 1))
        -- Add control links between instructions
        linkCode :: Map Label Node -> (Gr String (), Int) -> Code -> (Gr String (), Int)
        linkCode labelMap (g, next) (label, instrs) = 
          let predNode = labelMap ! label
              (g', (_, next')) = foldl (linkInstr labelMap) (g, (predNode, next)) instrs
          in (g', next')
        -- Adds all labels to the graph and creates a map from
        -- labels to nodes.
        mkLabelGraph :: (Gr String (), (Map Label Node, Int)) -> Code -> (Gr String (), (Map Label Node, Int))
        mkLabelGraph (g, (labelMap, next)) (label, instrs) = 
          let labNode = (emptyAdj
                        , next
                        , label
                        , emptyAdj)
              addInstrLabels :: (Gr String (), (Map Label Node, Int)) -> Instr -> (Gr String (), (Map Label Node, Int))
              addInstrLabels (g, (labelMap, next)) (Label l) = 
                let labNode = (emptyAdj
                              , next
                              , l
                              , emptyAdj)
                in (labNode & g, (Map.insert l next labelMap, next + 1))
              addInstrLabels s _ = s
          in foldl addInstrLabels (labNode & g, (Map.insert label next labelMap, next + 1)) instrs
        getCode (C.Body _ _ c) = c
        getCode (C.Capture l cnt (T target) r) = [(l, [H.Capture r target cnt])]
        -- Gets all code blocks from all groups
        blocks = concatMap getCode groups
        (labGraph, (labMap, nextNode)) :: (Gr String (), (Map Label Node, Int)) = foldl mkLabelGraph (G.empty, (Map.empty, 0)) blocks
    in fst $ foldl (linkCode labMap) (labGraph, nextNode) blocks

showInstr :: Instr -> String
showInstr (Enter _ _ _) = "Enter"
showInstr (Ret _) = "Ret"
showInstr (MkClo _ lab _) = "AllocC " ++ lab
showInstr (AllocD _ tag _) = "AllocD " ++ tag
showInstr (Copy _ _) = "Copy"
showInstr (Store _ _) = "Store"
showInstr (Load _ _) = "Load"
showInstr (Set _ _) = "Set"
showInstr (FailT _ tag _ _) = "FailT " ++ tag
showInstr (Label _) = "Label"
showInstr (Halt) = "Halt"
showInstr (Jmp _) = "Jmp"
showInstr (Error _) = "Error"
showInstr (Note _) = "Note"
showInstr (MkClo _ _ _) = "MkClo"
showInstr (Capture _ _ _) = "Capture"

writeViz :: String -> Gr String () -> IO () 
writeViz file gr = do
  let viz = graphviz' gr
  withFile (file ++ ".dot") WriteMode (\h -> hPutStr h viz)
        
