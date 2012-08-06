module Habit.Compiler.Stack.Eval
{- 

This file is designed to allow Habit programs to be compiled and/or
executed from GHCi. It works with MachineS/CompilerS/InterpS.

-}

where

import System.IO
import System.Exit
import System.Environment
import System.FilePath
import Control.Monad(forM_)
import Data.Graph(SCC(..))
import Data.Supply
import Data.Either
import Control.Monad (liftM)
import Data.List (intercalate)

import Habit.Options
import Habit.Passes

import Habit.Syntax.AST
import Habit.Syntax.Utils
import Habit.Syntax.IFace

import Habit.Session
import Habit.Compiler.Stack.Compiler (compile)
import Habit.Compiler.Stack.Machine (Instr(..), Machine(..), Program(..)
                                     , Val(..), runMachine, showVal)

-- | Evaluate the program in the givne file and 
-- return the result. IF an error occurs, Left
-- is returned. Otherwise, Right.
eval :: FilePath -> IO (Either String Val)
eval path = do
  supply <- newNumSupply
  let opts = default_options { opt_iface_paths = [opt_out_path default_options] }
      compile_mod _ (CyclicSCC _) = Left "Cycle module."
      compile_mod supply (AcyclicSCC m) = 
          Right $ compile supply (the_ast . get_pass $ m)
      load_file path = do
          fs <- load_files [path]
          return $ head fs
  (result, _) <- run_session opts (load_file path)
  return $ case result of
    Left err -> Left . show $ err
    Right p -> 
        case compile_mod supply p of
          Left err -> Left err
          Right is -> runProgram $ is

-- | Show the result of executing the given
-- file.
showEval :: FilePath -> IO String
showEval path = eval path >>= return . either show show 
  
runProgram :: [Instr] -> Either String Val
runProgram program = 
    case snd .  testProgramP $ program of
      (Machine { programC = Program _ (Error err) _ }) ->
          Left err
      m@(Machine { programC = Program _ Halt _ 
                 , workStack = (v:_) }) ->
          Right v
      m -> Left $ "Machine did not halt as expected: " ++ showTrace m

testProgram file = do
    (start, end) <- liftM testProgramP . readCode $ file
    putStrLn header
    putStrLn $ showTrace start
    putStrLn "..."
    putStrLn $ showResult end

traceProgram file = do
    trace <- liftM traceProgramP . readCode $ file
    putStrLn header
    mapM_ (putStrLn . showTrace) (init trace)
    putStrLn . showResult $ last trace

readCode :: String -> IO [Instr]
readCode = liftM readCodeP . readFile

testProgramP prog = (head trace
                    , last trace)
  where
    trace = traceProgramP prog

traceProgramP prog = runMachine prog

readCodeP :: String -> [Instr]
readCodeP = filter (not . isNote) . map read . lines
  where
    isNote (Note _) = True
    isNote _ = False

header = "Instruction | Working Stack | Call Stack | Stack Pointer | Match Stack\n" ++
         "----------------------------------------------------------------------" 

showTrace :: Machine -> String
showTrace (Machine { workStack = ws
                   , callStack = cs 
                   , programC = (Program _ instr _)
                   , stackLoc = sp
                   , matchStack = mss })
    = show instr ++ " | " ++ showTopS ws ++ " | " ++ 
      showTopCS cs ++ " | " ++ show sp ++ " | " ++ showTopMatchS mss
  where
    showTopS ws = "[(" ++ (show $ length ws) ++ ")]"
    showTopCS [] = "[]"
    showTopCS ((sp, ws, is):_) = "[(" ++ show sp ++ ", " ++
                             showTopS ws ++ ", " ++ "_), _]"
    showTopMatchS mss = "[(" ++ (show $ length mss) ++ ")]"

showResult (Machine { workStack = (w:ws)
                   , programC = (Program _ Halt _) })
    = show Halt ++ " | [" ++ showVal w ++ ", _] ... "
showResult machine = showTrace machine
