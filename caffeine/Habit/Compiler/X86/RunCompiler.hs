{-# LANGUAGE CPP #-}
import System.IO
import System.Exit
import System.Environment
import System.FilePath
import System.Cmd
import Control.Monad(forM_)
import Data.Graph(SCC(..))
import Data.Supply

import Habit.Options
import Habit.Passes

import Habit.Syntax.AST
import Habit.Syntax.Utils
import Habit.Syntax.IFace
import Habit.Utils.PP
import Habit.Utils.Misc(breaks)

import Habit.Session
import Habit.Compiler.Register.Compiler (compile, getInstrs, Group)
import Habit.Compiler.Register.Machine (Instr(Note))
import Habit.Compiler.X86.Compiler (assemble)

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
act a params = case a of
  Check ->
    case params of
      -- XXX: This check probably should not be here...
      [] -> io $ do hPutStrLn stderr "Please specify which files to check."
                    exitFailure
      _  -> mapM_ save_typed_mod_dump =<< load_files params

  -- Querying interfaces
  List -> with_mods params $ \m -> (io . putStrLn . ppsh) =<< get_iface m

  -- XXX: allow for more names?
  ShowKind name_txt ->
    with_mods params $ \m ->
      do let name = qual m name_txt
         kind <- query_kind m name
         io $ putStrLn (ppsh kind)

  ShowType name_txt ->
    with_mods params $ \m ->
      do let name = qual m name_txt
         ty <- query_type m name
         io $ putStrLn (ppsh ty)

        -- XXX: Use parser
  where parse_mod_name x = case breaks ('.'==) x of
                             [] -> crash $ OtherError
                                         $ "Invalid module name: " ++ x
                             xs -> return (ModName (init xs) (last xs))

        with_mods xs f = forM_ xs (\m -> f =<< parse_mod_name m)



query_kind :: ModName -> Name -> SessionM Kind
query_kind m n =
  do iface <- get_iface m
     case get_tcon iface n of
       Just tc -> return (kind_of tc)
       Nothing -> crash $ OtherError
                        $ "No kind information about: " ++ ppsh n

query_type :: ModName -> Name -> SessionM Schema
query_type m n =
  do iface <- get_iface m
     case get_schema iface n of
       Just s   -> return s
       Nothing  -> crash $ OtherError
                         $ "No type information about: " ++ ppsh n





--------------------------------------------------------------------------------

dump_typed_mod :: Module -> Doc
dump_typed_mod m =
   vsep (map (\(l, f) -> text l <+> f m) 
         [("mod_name: ", text . show . mod_name)
         -- , ("mod_exports: ", text . show . mod_exports)
         -- , ("mod_imports: ", text . show . mod_imports)
         , ("mod_data: ", vsep . punctuate comma . map ppData . mod_data)
         -- , ("mod_bitdata: ", text . show . mod_bitdata)
         -- , ("mod_classes: ", text . show . mod_classes)
         -- , ("mod_instances: ", text . show . mod_instances)
         -- , ("mod_prim_types: ", text . show . mod_prim_types)
         , ("mod_decls: ", ppDecls . mod_decls)
         , ("mod_prims: ", text . show . mod_prims)
         , ("mod_ty_fixities: ", text . show . mod_ty_fixities)])
                --   text "module" <+> pp (mod_name m) $$
                --   pp (mod_decls m) $$
                --   vsep (map pp (mod_prims m))
  where
    ppDecls :: Decls -> Doc
    ppDecls (Decls { expl_decls = expl
                   , impl_decls = imp
                   , ev_decls = ev 
                   , fixities = fix }) = text "expl_decls: " <+> (vsep . punctuate comma $ (map ppExplDecl expl)) $+$
                                         text "impl_decls: " <+> (vsep . punctuate comma $ (map ppImplDecl imp)) $+$
                                         text "ev_decls: " <+> (vsep . punctuate comma $ (map pp ev)) $+$
                                         text "fixities: " <+>  (text . show $ fix)
    ppExplDecl (ExplDecl { decl = exp_decl
                        , sig = sign }) = text "sig: " <+> pp sign $+$
                                          text "decl: " <+> ppImplDecl exp_decl
    ppImplDecl (ImplDecl { decl_name = name
                         , decl_tparams = tparams
                         , decl_eparams = eparams
                         , decl_body = body}) = text "decl_name: " <+> ppName name $+$
                                                text "decl_tparams: " <+> (vcat . punctuate comma $ (map pp tparams)) $+$
                                                text "decl_eparams: " <+> (vsep . punctuate comma $ (map pp eparams)) $+$
                                                text "decl_body: " <+> ppMatch body
    ppMatch (MPat pat match) = hang (text "mpat:" <+> pp pat) 2 (ppMatch match)
    ppMatch (MGrd guard match) = hang (text "grd:" <+> ppGuard guard) 2 (ppMatch match)
    ppMatch (MAlt match1 match2) = hang (text "alt1: ") 2 (ppMatch match1) $+$ hang (text "alt2: ") 2 (ppMatch match2)
    ppMatch (MExp expr) = hang (text "expr: ") 2 (ppExpr expr)
    ppMatch (MFail _) = text "FAIL"   -- XXX: Take arity into account?
    ppGuard (GMatch pat expr) = text "GMatch: pat: " <+> pp pat $+$
                                text "expr: " <+> ppExpr expr
    ppGuard (GLet decls) = text "GLet: decls: " <+> ppDecls decls
    ppExpr (EApp expr1 expr2) = braces $ text "app:" $$ parens (nest 2 (ppExpr expr1)) $+$
                                parens (nest 2 (ppExpr expr2))
    ppExpr (ELet decls expr) = (hang (text "let: ") 2 (ppDecls $ decls)) $+$
                               hang (text "in:") 2 (ppExpr expr)
    ppExpr (EAbs match) = text "abs: " <+> ppMatch match
    ppExpr (ECase expr match) = hang (text "case: ") 2 (ppExpr expr) $+$
                                hang (text "of: ") 2 (ppMatch match)
    ppExpr (EInfix expr1 name expr2) = hang (text "op:" <+> ppName name) 2 
                                        ((hang (text "left: ") 2 (ppExpr expr1)) $+$
                                        (hang (text "right: ") 2 (ppExpr expr2)))
    ppExpr (EParens expr) = parens (ppExpr expr)

    ppExpr exp@(EVar (EV name _ _)) = ppName name
    ppExpr exp@(ELit literal) = pp exp

    ppData (Data { data_name = name
                 , data_params = params
                 , data_cons = cons }) 
        = hang (text "data:" <+> ppTCon name <+> parens (hcat . punctuate comma . map pp $ params)) 2
               (vcat . punctuate comma . map ppDataConn $ cons)
    ppDataConn (DataCon { data_con_name = name
                        , data_con_fields = fields }) 
        = text "constructor:" <+> ppName name
    ppName (Name Nothing name _) = text name
    ppName (Name (Just qual) name _) = text (show qual ++ name)
    ppTCon (TC name _) = ppName name
    ppTCon tc = pp tc

save_typed_mod_dump :: SCC TypedModule -> SessionM ()
save_typed_mod_dump (CyclicSCC {}) = crash $ OtherError
                                           $ "Cyclic SCC"
save_typed_mod_dump (AcyclicSCC mo) =
  do let m = the_ast (get_pass mo)
     opts <- get_cmd_opts
     supply <- io newNumSupply
     let env = default_pp_env { pp_opts = opt_pp opts }
         funcs = compile supply m
         file_name = mod_name_to_file (mod_name m)
     save_file (file_name <.> "dump")
                   $ show $ run_pp_with env $ dump_typed_mod m
#ifdef DEBUG
     let showCode instrs = map (\i -> show i) instrs
#else 
     let showCode instrs = map (\i -> show i) . filter notNote $ instrs
         notNote (Note _) = False
         notNote _ = True
#endif
     let showFuncs (l, size, codes) = "Group " ++ l ++ " (" ++ show size ++ ") \n" ++ 
                                (unlines . map ("  " ++) . 
                                 concatMap (\(l, cs) -> (l ++ ":") : showCode cs) $ codes)
     save_file (file_name <.> ".r.hs") (unlines . showCode . getInstrs $ funcs)
     save_file (file_name <.> ".f.hs") $ concatMap showFuncs funcs
     save_file (file_name <.> ".s") . unlines . assemble supply $ funcs
     _ <- io (system $ "gcc -g -o " ++ file_name ++ " ifaces/" ++ file_name <.> ".s" ++ 
          " runtime.c")
     return ()


