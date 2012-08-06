module Habit.Compiler.Register.PrintModule (dump_typed_mod)

where

import Habit.Syntax.AST
import Habit.Utils.PP

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
         , ("mod_prim_types: ", text . show . mod_prim_types)
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
                                         text "impl_decls: " <+> (vsep . punctuate comma $ (map pp imp)) $+$
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
    ppMatch (MGrd guard match) = hang (text "grd:" <+> text (show guard)) 2 (ppMatch match)
    ppMatch (MAlt match1 match2) = hang (text "alt1: ") 2 (ppMatch match1) $+$ hang (text "alt2: ") 2 (ppMatch match2)
    ppMatch (MExp expr) = hang (text "expr: ") 2 (ppExpr expr)
    ppMatch (MFail _) = text "FAIL"   -- XXX: Take arity into account?
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
    ppName (Name (Just qual) name _) = text ("[...]." ++ name)
    ppTCon (TC name _) = ppName name
    ppTCon tc = pp tc

