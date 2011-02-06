{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
module Printer.LambdaCase (module Printer.LambdaCase, Printable(..)) where

-- This file began as a copy of Printer.XMPEG

import Printer.Common
import Syntax.Common
import Syntax.LambdaCase

-- Also in XMPEG:

instance Printable (Kinded Id)
    where ppr (Kinded id k) = parens (ppr id <+> text "::" <+> ppr k)

instance Printable Type
    where ppr (TyCon id)   = ppr id
          ppr (TyApp t t') = atPrecendence 9 (ppr t <+> withPrecedence 10 (ppr t'))
          ppr (TyLit i)    = integer i 
          ppr (TyLabel l)  = text "Lab " <+> text l

----------------------------------------------------------------------------------------------------
instance Printable (Syntax.LambdaCase.Literal)
    where ppr (Lit l t) = parens (integer l <+> text "::" <+> ppr t)

instance Printable Expr
    where ppr (EVar id)         = ppr id
          ppr (EPrim id ts)     = angles $ align $ ppr id <+> (align (cat (punctuate comma (map ppr ts))))
          ppr (ELit l)          = ppr l
          ppr (ECon id ts es)   = atPrecendence 9 $
                                  ppr id <> braces (cat (punctuate comma (map ppr ts)))
                                         <> braces (cat (punctuate comma (map ppr es))) 
          ppr (ELam id ty body) = backslash <+> ppr id <+> text "::" <+> ppr ty </> text "->" <+> align (ppr body)
          ppr (ELet ds body)    = text "let" <+> align (ppr ds) </> text "in" <+> (align (ppr body))
          ppr (ECase e alts)    = align $ text "case" <+> parens (ppr e) <$> text "of" <+>
                                  (braces $ align $ hcat $ punctuate (line <> bar) $ map (align . ppr) alts)
          ppr (EApp e e')       = atPrecendence 9 (ppr e <$> indent 3 (withPrecedence 10 (ppr e')))
          ppr (EFatbar e e')    = brackets ((align (ppr e)) </> text "||" <+> (align (ppr e')))  -- could use precedence here
          ppr (EBind "_" _ e body) = braces $ align $
                                (align (ppr e)) <+> semi <$> 
                                ppr body
          ppr (EBind var varty e body) = braces $ align $
                                ppr var <+> text "::" <+> ppr varty </> text "<-" <+> (align (ppr e)) <+> semi <$> 
                                ppr body

instance Printable Alt
    where ppr (Alt c [] [] e)   = ppr c <+> text "->" <+> (align (ppr e))
          ppr (Alt c tys ids e) = ppr c <+> (cat (punctuate comma (map ppr ids))) <+> text "::"
                                <+> (cat (punctuate comma (map ppr tys)))  </> text "->" <+> (align (ppr e))

instance Printable Decls
    where ppr (Decls dss) = semiBraces (map pprScc dss)
              where 
--                pprScc ds = brackets (cat (punctuate (semi <> line) (map pprDecl ds)))
                pprScc ds = semiBraces (map pprDecl ds)
                pprDecl (i,t,e) = ppr i <+> nest 5 (text "::" <+> ppr t </> text "=" <+> (nest 3 $ ppr e))

instance Printable TopDecl
    where ppr (Datatype name params ctors) = nest 4 (text "data" <+> symbol name <+> cat (punctuate space (map ppr params)) <> pprCtors)
              where pprCtor (name, fields) = ppr name <+> sep (map (atPrecendence 10 . ppr) fields)
                    pprCtors =
                        case ctors of
                          [] -> empty
                          (first : rest) -> equals <+> pprCtor first <> cat [ softline <> bar <+> pprCtor ctor | ctor <- rest ]
          
          ppr (Bitdatatype name size ctors) = nest 4 (text "bitdata" <+> symbol name <> (int size) <> pprCtors )
              where pprCtor (name, fields) = ppr name <+> brackets (cat (punctuate (space <> bar <> space) (map ppr fields)))
                    pprCtors =
                        case ctors of
                          [] -> empty
                          (first : rest) -> equals <+> pprCtor first <> cat [ softline <> bar <+> pprCtor ctor | ctor <- rest ]

          ppr (Struct name size regions) = 
              nest 4 (ppr name <> int size <+> brackets (cat (punctuate (softline <> bar <> space) (map ppr regions))) )

          ppr (Area ids ty) = 
              nest 4 (text "area" <+> cat (punctuate (comma <> softline) [ ppr name <+> text "=" <+> ppr init | (name, init) <- ids ])
                               </> text "::" <+> ppr ty)

instance Printable BitdataField
    where ppr (LabeledField name ty init) = 
              text name <> maybe empty (\init -> space <> equals <+> ppr init) init <+> text "::" <+> ppr ty 
          ppr (ConstantField e) = ppr e

instance Printable StructRegion
    where ppr (StructRegion Nothing ty) = ppr ty
          ppr (StructRegion (Just (StructField id Nothing)) ty) = ppr id <+> text "::" <+> ppr ty
          ppr (StructRegion (Just (StructField id (Just init))) ty) = ppr id <+> text "<-" <+> ppr init <+> text "::" <+> ppr ty

instance Printable Program
    where ppr p = vcat (punctuate line (map ppr (topDecls p) ++
                                        [ppr (decls p)]))
