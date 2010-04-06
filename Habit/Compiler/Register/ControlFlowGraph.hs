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
    let node (Just prev) n lbl = ([((), prev)]
                                 , n
                                 , lbl
                                 , [] :: [((), Node)])
        node Nothing n lbl = ([] :: [((), Node)]
                             , n
                             , lbl
                             , []  :: [((), Node)])
        emptyAdj = [] :: [((), Node)]
        addLabels (g, m) blocks =
          let addLabel (s, n) (Label l) = ((emptyAdj
                                           , n
                                           , l
                                           , emptyAdj) & s, n + 1)
              addLabel (s, n) _ = (s, n)
          in foldl addLabel (g, m) . concatMap snd $ blocks
        mkSubGraph (g, (prev, n)) (_, _, blocks) = 
          let (subgraph, n') = foldl addLabels (g, n) blocks
          in (subgraph, (Just n', n' + 1))
        -- Graph of groups
    in fst $ foldl mkSubGraph (empty, (Nothing, 0)) groups

writeViz gr = do
  let viz = graphviz' gr
  withFile "graph.viz" WriteMode (\h -> hPutStr h viz)
        
