module Habit.Compiler.Register.Eval
{- 

This file is designed to allow Habit programs to be compiled and/or
executed from GHCi. It works with MachineS/CompilerS/InterpS.

-}

where

import System.IO
import Control.Monad(liftM)
import Data.Graph(SCC(..))
import Data.Supply
import Data.Maybe
import Data.List (intercalate)

import Habit.Options
import Habit.Passes
import Habit.Session
import Habit.Syntax.AST (Module)

import Habit.Compiler.Register.Compiler (compile, getInstrs, Group)
import Habit.Compiler.Register.Machine (Instr(..), Machine(..), Program(..)
                                        , Val(..), getRegister, resultReg
                                        , runMachine, argReg, cloReg)

-- | Evaluate the program in the givne file and 
-- return the result. IF an error occurs, Left
-- is returned. Otherwise, Right.
eval :: FilePath -> IO (Either String Val)
eval path = do
  mod <- parseModule path
  supply <- newNumSupply
  return $ case mod of
    Left err -> Left . show $ err
    Right p -> runProgram . getInstrs . compile supply $ p

parseModule :: FilePath -> IO (Either String Module)
parseModule path = do
  let opts = default_options { opt_iface_paths = [opt_out_path default_options]
                             , opt_quiet = True }
      load_file path = do
          fs <- load_files [path]
          return $ head fs
  (result, _) <- run_session opts (load_file path)
  return $ case result of
    Left err -> Left . show $ err
    Right (AcyclicSCC p) -> Right . the_ast . get_pass $ p
    _  -> Left "Unable to parse module."

withModule :: FilePath -> (Supply Int -> Module -> IO a) -> IO a
withModule path act = do
  supply <- newNumSupply
  result <- parseModule path
  case result of
    Left err -> error err
    Right m -> act supply m

-- | show the result of executing the given
-- file.
showEval :: FilePath -> IO String
showEval path = eval path >>= return . either show show 
  
runProgram :: [Instr] -> Either String Val
runProgram program = 
    case snd .  testProgramP $ program of
      (Machine { program = Program _ (Error err) _ }) ->
          Left err
      m@(Machine { program = Program _ (Ret reg) _ 
                 , registers = rs }) -> maybe (Left "No result.")
                                              (Right)
                                              (getRegister rs reg)
      m -> Left $ "Machine did not halt as expected: " ++ showTrace m

header = "Instruction | Registers | Call Stack \n" ++
         "---------------------------------------"

showTrace :: Machine -> String
showTrace (Machine { program = (Program prev instr _)
                   , registers = regs
                   , callStack = cs })
    = show instr ++ " | " ++ showRegs
  where
    showTopS regs = ""
    showRegs = intercalate "," . map (\(r, v) -> r ++ ": " ++ showVal v) . 
               catMaybes . map (\r -> do { v <- getRegister regs r; return (r,v)}) $ 
               (gatherRegs instr ++ getPrevReg) 
    getPrevReg 
        | null prev = []
        | otherwise = gatherRegs (last prev)
    gatherRegs (Enter r1 r2 r3) = [r1, r2, r3]  
    gatherRegs (Ret r1) = [r1]
    gatherRegs (AllocC r1 _ _) = [r1]
    gatherRegs (AllocD r1 _ _) = [r1]
    gatherRegs (Copy r1 r2) = [r1, r2]
    gatherRegs (Store r1 (r2, _)) = [r1, r2]
    gatherRegs (Load (r1, _) r2) = [r1, r2]
    gatherRegs (Set r1 _) = [r1]
    gatherRegs (FailT r1 _ _) = [r1]
    gatherRegs _ = []
    showVal (Num i) = show i
    showVal (Data t vs) = "@" ++ t ++ " [" ++ intercalate "," (map showVal vs) ++ "]"
    showVal (Str s) = "\"" ++ s ++ "\""

testProgram file = do
    (start, end) <- liftM testProgramP . readCode $ file
    putStrLn header
    putStrLn $ showTrace start
    putStrLn "..."
    putStrLn $ showTrace end

traceProgram file = do
    trace <- liftM traceProgramP . readCode $ file
    putStrLn header
    mapM_ (putStrLn . showTrace) (init trace)
    putStrLn . showTrace $ last trace

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
