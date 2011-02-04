module Syntax.LambdaCase where

import Syntax.Common hiding (Literal(..))

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

data Type = TyCon (Kinded Id)
          | TyApp Type Type
          | TyLit Integer 
          | TyLabel Id

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

data Literal = Lit Integer Type

data Expr = EVar Id
          | EPrim Id [Type]
          | ELit Literal
          | ECon Id [Type] [Expr]
          | ELam Id Type Expr
          | ELet Decls Expr
          | ECase Expr [Alt]
          | EApp Expr Expr
          | EFatbar Expr Expr
          | EBind Id Type Expr Expr -- (id :: t) <- e ; e

data Alt = Alt Id [Type] [Id] Expr  -- (C::t) vs -> e

--------------------------------------------------------------------------------
-- Declarations
--------------------------------------------------------------------------------

data Decls = Decls [[(Id, Type, Expr)]] -- maintained in topological order

--------------------------------------------------------------------------------
-- Top-level declarations
--------------------------------------------------------------------------------

-- bitdata T = S [B010 | x :: Ix 32] | Q [ y :: Bit 8 ]

data TopDecl = Datatype Id                         -- name
                        [Kinded Id]                -- params
                        [(Id, [Type])]             -- ctors
             -- When do we convert bitdata operations to word operations?
             | Bitdatatype Id                      -- name
                           Int                     -- width
                           [(Id, [BitdataField])]  -- params
             | Struct Id                           -- structure nam
                      Int                          -- width
                      [StructRegion]               -- regions
             | Area [(Id, Expr)]                   -- names and initializers
                    Type                           -- type
               -- Area-local definitions lifted to top level

data BitdataField = LabeledField Id Type (Maybe Expr) -- more about the widths of the fields? 
                  | ConstantField Literal
data StructRegion = StructRegion (Maybe StructField) Type
data StructField = StructField Id (Maybe Expr)

type TopDecls = [TopDecl]

--------------------------------------------------------------------------------

data Program = Program { decls        :: Decls
                       , topDecls     :: TopDecls }

--------------------------------------------------------------------------------
