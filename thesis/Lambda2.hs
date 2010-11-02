module Lambda2

where

import Prelude hiding (abs, not)
import Text.PrettyPrint 
import Data.List (intersperse)


main = putStrLn . render . printDefs $ [nil, not, notNil]

{-

The lambda-calculus with cases and algebraic data types. Expressions
in the language include:

  expr ::= \x . e  -- abstraction
       |   e1 e2   -- application
       |   v       -- variables
       |   case e1 of [alt1, ..., altN] -- Case discrimination
       |   C e1 ... eN -- Constructor 

  alt ::= C v1 ... vN -> e

-}

type Name = String
type Var = String
type Constructor = String

data Expr = Abs Var Expr
          | App Expr Expr
          | Var Var
          | Case Expr [Alt]
          | Constr Constructor [Expr]
  deriving (Show, Eq)

data Alt = Alt Constructor [Name] Expr
  deriving (Show, Eq)

type Def = (Name, Expr)

abs :: Var -> (Expr -> Expr) -> Expr
abs v f = Abs v (f (Var v))

false :: Expr
false = Constr "False" []

true :: Expr
true = Constr "True" []

nil :: Def 
nil = ("nil", nilDef)
  where
    nilDef = abs "xs" $ \xs -> Case xs [Alt "Nil" [] true
                                       , Alt "Cons" ["a", "b"] false]
not :: Def
not = ("not", notDef)
  where
    notDef = abs "f" $ \f -> Case f [Alt "True" [] false
                                    , Alt "False" [] true]

notNil :: Def
notNil = ("notNil", notNilDef)
  where
    notNilDef = abs "xs" $ \xs -> App (Var "not") (App (Var "nil") xs)

printDefs :: [Def] -> Doc
printDefs ds = vcat' 
               . intersperse (text (replicate 72 '=')) 
               . map printDef $ ds

printDef :: Def -> Doc
printDef (name, body) = hang (text name <+> text "=") 2 (printExpr body) 

printExpr :: Expr -> Doc
printExpr (Abs var e) = text "\\" <> text var <> text "." <+> printExpr e
printExpr (App e1 e2) = printVar e1 <+> printVar e2
printExpr (Var v) = text v
printExpr (Case e alts) = hang (text "case" <+> printExpr e <+> text "of") 2 (vcat' . map printAlt $ alts)
  where
    printAlt (Alt cons vs e) = text cons <+> (hsep . map text $ vs) <+> text "->" <+> printExpr e
printExpr (Constr cons exprs) = text cons <+> (hsep . map printVar $ exprs)

printVar (Var v) = text v
printVar e = parens (printExpr e)

vcat' :: [Doc] -> Doc
vcat' = foldl ($+$) empty
