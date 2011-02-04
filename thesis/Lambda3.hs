{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module Lambda3

where

import Text.PrettyPrint 
import Data.List ((\\), nub, delete)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Util

{-

The lambda-calculus with cases and algebraic data types. Expressions
in the language include:

  expr ::= \x {fvs}. e  -- abstraction w/ free variables annotated
       |   e1 e2   -- application
       |   v       -- variables
       |   case e1 of [alt1, ..., altN] -- Case discrimination
       |   C e1 ... eN -- Constructor 

  alt ::= C v1 ... vN -> e

A program consists of multiple, possibly recursive, top-level
definitions:

  def ::= f = expr

  prog ::= def1
           ...
           defN
-}

data Expr = Abs Var Free Expr
          | App Expr Expr
          | Var Var
          | Case Expr [Alt Expr]
          | Constr Constructor [Expr]
  deriving (Show, Eq)

type Free = [Name] 
type Def = (Name, Expr)
type Prog = [Def]

-- | Annotate lambda-calculus programs with free variables and
-- rename variables so we can always generate safe fresh names.
prepareExpr :: [Name] -> Prog -> Prog
prepareExpr tops = addFVs . renameVars 
  where
    addFVs = map (\(name, body) -> (name, snd $ annotate body))
    -- All variables have an underscore attached. The compiler will
    -- never generate variables with underscores, guaranteeing
    -- it can always create a fresh variable name.
    renameVars = map (\(name, body) -> (name, renameInExpr Map.empty body))
    renameInExpr :: Map Name Name -> Expr -> Expr
    renameInExpr env (Abs vs [] b) = 
      let ([vs'], env') = addNames env [vs]
      in Abs vs' [] (renameInExpr env' b)
    renameInExpr env (App e1 e2) = App (renameInExpr env e1) (renameInExpr env e2)
    renameInExpr env (Case e alts) = 
      let alts' = map (renameAlt env) alts
      in Case (renameInExpr env e) alts'
    renameInExpr env (Constr c exprs) = 
      Constr c (map (renameInExpr env) exprs)
    renameInExpr env (Var v) 
                 | v `Map.member` env  = Var (env ! v)
                 | otherwise = Var v
    renameAlt env (Alt c ns e) = 
      let (ns', env') = addNames env ns
      in Alt c ns' (renameInExpr env' e)
    addNames env vs = 
      let vs' = map (++ "_") vs
      in  (vs', env `Map.union` Map.fromList (zip vs vs'))
    -- Add free variables to each lambda.
    annotate :: Expr -> (Free, Expr)
    annotate (Abs v _ expr)   
      = let (fvs, expr') = annotate expr
            fvs'         = delete v (nub fvs)
        in (fvs', Abs v fvs' expr')
    annotate (App e1 e2)      
      = let (fvs1, e1') = annotate e1
            (fvs2, e2') = annotate e2
        in (fvs1 ++ fvs2, App e1' e2')
    annotate e@(Var v)  
      | v `elem` tops = ([], e)
      | otherwise = ([v], e)
    annotate (Case e alts)    
      = let (fvs1, e')    = annotate e
            (fvs2, alts') = unzip $ map annotateAlt alts
        in (fvs1 ++ concat fvs2, Case e' alts')
    annotate (Constr c exprs) 
      = let (fvs1, exprs') = unzip $ map annotate exprs
        in (concat fvs1, Constr c exprs')
    annotateAlt (Alt c ns e) 
      = let (fvs, e') = annotate e
        in (fvs \\ ns, Alt c ns e')

-- Printing lambda-calculus terms

printDef :: Def -> Doc
printDef (name, body) = hang (text name <+> text "=") 2 (printExpr body) 

printExpr :: Expr -> Doc
printExpr (Abs var fvs e) = text "\\" <> text var <+> braces (hsep (punctuate comma (texts fvs))) <>  text "." <+> printExpr e
printExpr (App e1 e2) = printVar e1 <+> printVar e2
printExpr (Var v) = text v
printExpr (Case e alts) = hang (text "case" <+> printExpr e <+> text "of") 2 (vcat' . map printAlt $ alts)
  where
    printAlt (Alt cons vs e) = text cons <+> (hsep (texts vs)) <+> text "->" <+> printExpr e
printExpr (Constr cons exprs) = text cons <+> (hsep . map printVar $ exprs)

printVar (Var v) = text v
printVar e = parens (printExpr e)


