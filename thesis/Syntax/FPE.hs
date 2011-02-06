module Syntax.FPE (module Syntax.FPE, module Syntax.Common)  where

import Data.Map (Map)
import qualified Data.Map as Map
import Syntax.Common

--------------------------------------------------------------------------------
-- Kinds and types
--------------------------------------------------------------------------------

data Type = TyCon Id
          | TyVar Id
          | TyApp (Located Type) (Located Type)
          | TyLit Integer 
          | TyKinded (Located Type) (Located Kind)
          | TyLabel Id
          | TySelect (Located Type) (Located Id)
          | TyInfix (Located Type) [(Located Id, Located Type)]
            deriving Show

--------------------------------------------------------------------------------
-- Predicates and qualifiers
--------------------------------------------------------------------------------

data Pred = Pred (Located Type) (Maybe (Located Type)) Flag
            deriving Show

data Qual t = [Located Pred] :=> Located t
              deriving Show

--------------------------------------------------------------------------------
-- Expressions and statements
--------------------------------------------------------------------------------

data Expr = ELet Decls (Located Expr)
          | EIf Scrutinee (Located Expr) (Located Expr) -- Parser will inject magical "return ()" in if statements
          | ECase Scrutinee [Alt]
          | ELam [Located Pattern] (Located Expr) 
          | EVar Id
          | ECon Id
          | ELit Literal
          | EApp (Located Expr) (Located Expr)
          | EBind (Maybe (Located Id)) (Located Expr) (Located Expr)
          | ESelect (Located Expr) (Located Id)
          | EUpdate (Located Expr) [(Located Id, Located Expr)]
          | ELeftSection (Located Expr) (Located Id)
          | ERightSection (Located Id) (Located Expr)
          | EStructInit (Located Id) [(Located Id, Located Expr)]
          | ETyped (Located Expr) (Qual Type)
          | EInfix (Located Expr) [(Located Id, Located Expr)]
            deriving Show

data Scrutinee = ScExpr (Located Expr)
               | ScFrom (Located Expr)
               deriving Show

data Alt = Located Pattern :-> Rhs deriving Show

--------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------

data Pattern = PVar Id
             | PLit Literal
             | PWild
             | PAs Id (Located Pattern)
             | PTyped (Located Pattern) (Qual Type)
             | PCon Id
             | PApp (Located Pattern) (Located Pattern)
             | PBitdata Id [Located FieldPattern]
             | PInfix (Located Pattern) [(Located Id, Located Pattern)] 
               deriving Show

flattenPattern :: Located Pattern -> (Located Pattern, [Located Pattern])
flattenPattern (At _ (PApp lhs rhs)) = (op, ps ++ [rhs])
    where (op, ps) = flattenPattern lhs
flattenPattern p = (p, [])

data FieldPattern = FieldPattern Id (Maybe (Located Pattern))
                    deriving Show

--------------------------------------------------------------------------------
-- Declarations
--------------------------------------------------------------------------------

data Equation = Located Pattern := Rhs
              deriving Show

data Rhs = Unguarded (Located Expr) (Maybe Decls)
         | Guarded [(Located Expr, Located Expr)] (Maybe Decls) -- List of (guard, body)
           deriving Show

--

data Assoc = LeftAssoc | RightAssoc | NoAssoc
             deriving Show

data Fixity = Fixity Assoc Int 
              deriving Show

data Fixities = Fixities { valFixities :: Map Id (Located Fixity)
                         , typeFixities :: Map Id (Located Fixity) } 
                deriving Show


mergeFixities :: Fixities -> Fixities -> Fixities
mergeFixities old new = Fixities (Map.unionWith second (valFixities old) (valFixities new))
                                 (Map.unionWith second (typeFixities old) (typeFixities new))
    where second _ x = x

emptyFixities = Fixities Map.empty Map.empty

--

data Signature = Signature Id (Qual Type)
                 deriving Show

--

data Decls = Decls { equations  :: [Equation]
                   , signatures :: [Signature]
                   , fixities   :: Fixities } 
             deriving Show

emptyDecls = Decls [] [] (Fixities Map.empty Map.empty)

--------------------------------------------------------------------------------
-- Classes and instances
--------------------------------------------------------------------------------

-- Introduce TypeLhs?

data Class = Class (Located Type) [Located ClassConstraint] (Maybe Decls)
                 deriving Show
data ClassConstraint = Superclass Pred | Fundep (Fundep Id)
                       deriving Show

data Instance = Instance [(Qual Pred, Maybe Decls)]
                  deriving Show

--------------------------------------------------------------------------------
-- Type synonyms and data declarations
--------------------------------------------------------------------------------

data Synonym = Synonym (Located Type) (Qual Type)
               deriving Show

data Datatype = Datatype (Located Type)                 -- name and params
                         [Ctor Pred Type]
                         [Id]                           -- deriving list
                deriving Show

--------------------------------------------------------------------------------
-- Bitdata and areas
--------------------------------------------------------------------------------

data Bitdatatype = Bitdatatype Id           
                               (Maybe (Qual Type))
                               [Ctor Pred BitdataField]
                               [Id] -- deriving list
                 deriving Show

data BitdataField = LabeledField Id (Located Type) (Maybe (Located Expr))
                  | ConstantField (Located Expr)
                  deriving Show

data Struct = Struct Id (Maybe (Qual Type)) [StructRegion] [Id]
              deriving Show
data StructRegion = StructRegion (Maybe StructField) (Qual Type)
                  deriving Show
data StructField = StructField (Located Id) (Maybe (Located Expr))
                 deriving Show

data Area = Area [(Located Id, Maybe (Located Expr))] (Qual Type) (Maybe Decls)
            deriving Show

--------------------------------------------------------------------------------

data Program = Program { decls        :: Decls
                       , classes      :: [Located Class]
                       , instances    :: [Located Instance]
                       , synonyms     :: [Located Synonym]
                       , datatypes    :: [Located Datatype]
                       , bitdatatypes :: [Located Bitdatatype]
                       , structures   :: [Located Struct]
                       , areas        :: [Located Area] } 
               deriving Show

emptyProgram = Program { decls        = emptyDecls
                       , classes      = []
                       , instances    = []
                       , synonyms     = []
                       , datatypes    = []
                       , bitdatatypes = []
                       , structures   = []
                       , areas        = [] }
