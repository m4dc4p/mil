{-# LANGUAGE CPP #-}
import System.IO
import System.Exit
import System.Environment
import System.FilePath
import Control.Monad(forM_)
import Data.Graph(SCC(..))
import Data.Supply
import Compiler.Hoopl (runWithFuel)

import Habit.Options
import Habit.Passes

import Habit.Syntax.AST
import Habit.Syntax.Utils
import Habit.Syntax.IFace
import Habit.Utils.Misc(breaks)
import Habit.Utils.PP

import Habit.Session
import Habit.Compiler.Register.Compiler (compile, getInstrs, Group, Code)
import Habit.Compiler.Register.Machine (Instr(..))
import Habit.Compiler.Register.PrintModule (dump_typed_mod)
import Habit.Compiler.Register.ControlFlowGraph
import Habit.Compiler.Register.Dataflow 

main :: IO ()
main = parse_opts `fmap` getArgs >>= \res ->
  case res of
    (opts, xs, []) ->
      do r <- run_session_quiet opts (act (opt_action opts) xs)
         case r of
           Right a -> return a
           Left e ->
             do hPutStrLn stderr (ppsh e)
                exitFailure
    _ -> hPutStrLn stderr (usage "") >> exitFailure

act :: Action -> [String] -> SessionM ()
act Check params = 
  case params of
    -- XXX: This check probably should not be here...
    [] -> io $ do hPutStrLn stderr "Please specify which files to check."
                  exitFailure
    _  -> mapM_ (save_typed_mod_dump visualizer) =<< load_files params
act a _ = crash $ OtherError $ "Unsupported action " ++ show a

visualizer :: String -> [Group] -> SessionM [Group]
visualizer file gs = do
  io (writeViz file (makeCFG gs))
  let gs' = optGroups noOpOpt . 
            optGroups cloOpt .
            optGroups liveOpt .
            optGroups constPropOpt $ gs
  io (writeViz (file ++ ".opt") (makeCFG gs'))
  return gs'

noOp _ gs = return gs

--------------------------------------------------------------------------------

save_typed_mod_dump :: (String -> [Group] -> SessionM [Group]) -> SCC TypedModule -> SessionM ()
save_typed_mod_dump _ (CyclicSCC {}) = crash $ OtherError
                                           $ "Cyclic SCC"
save_typed_mod_dump optimizer (AcyclicSCC mo) =
  do let m = the_ast (get_pass mo)
     opts <- get_cmd_opts
     let env = default_pp_env { pp_opts = opt_pp opts }
         file_name = mod_name_to_file (mod_name m)
     supply <- io newNumSupply
     let unOptGroups = compile supply m
     optGroups <- optimizer file_name (removeNotes unOptGroups)
     save_file (file_name <.> "dump")
                   $ show $ run_pp_with env $ dump_typed_mod m
     save_files file_name unOptGroups optGroups

save_files :: String -> [Group] -> [Group] -> SessionM ()
save_files file_name unOpt opt = do
  let showFuncs (l, size, codes) = "Group " ++ l ++ " (" ++ show size ++ ") \n" ++ 
        (unlines . map ("  " ++) . concatMap (\(l, cs) -> (l ++ ":") : showCode cs) $ codes)
      no_groups prefix gs = do
        save_file (file_name <.> prefix <.> "r.hs") . showIR . removeNotes $ gs
        save_file (file_name <.> prefix <.> "r.note.hs") . showIR $ gs
      with_groups prefix gs = do
        save_file (file_name <.> prefix <.> ".f.hs") . concatMap showFuncs . removeNotes $ gs
        save_file (file_name <.> prefix <.> ".f.note.hs") . concatMap showFuncs $ gs
      showCode :: [Instr] -> [String]
      showCode instrs = map show instrs
      showIR :: [Group] -> String
      showIR = unlines . showCode . getInstrs 
  no_groups "" unOpt
  no_groups ".opt" opt
  with_groups "" unOpt
  with_groups ".opt" opt

removeNotes :: [Group] -> [Group]
removeNotes = 
  let removeNote (l, cs) = (l, filter notNote cs)
      notNote (Note _) = False
      notNote _ = True
  in map (\(l, c, css) -> (l, c, map removeNote css))
    
      

