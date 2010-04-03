import System.Environment (getArgs)
import Habit.Compiler.Register.Eval
import Habit.Compiler.Register.Machine

main = do
  file <- getArgs >>= return . head
  testProgram file

