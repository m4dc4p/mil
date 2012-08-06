import Habit.Compiler.Stack.Machine
import Habit.Compiler.Stack.Eval
import System.Environment (getArgs)

main = do
  file <- getArgs >>= return . head
  traceProgram file

