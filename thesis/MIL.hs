{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module MIL

where

import Prelude hiding (abs)
import Control.Monad.State (State, execState, modify, gets)
import Text.PrettyPrint 
import Data.List (sort)
import Data.Maybe (fromMaybe, isJust, catMaybes)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Compiler.Hoopl

import Util

type ProgM = Graph StmtM
type Dest = (Name, Label)

{-

Our monadic language:

  
  bodyM ::= do 
    stmtM1; 
    ... ; 
    stmtMN; 
    tailM

  stmtM ::= v <- tailM
    | case v of [alt1, ..., altN]
    | tailM

  tailM ::= return v
    | v1 @ v2         -- Call an unknown function.
    | f(v1, ..., v)  -- Goto a known block.
    | closure f {v1, ..., vN} -- Create closure pointing to a function.

  alt ::= C v1 ... vN -> call f(u1, ..., uM)

  defM ::= f {v1, ..., vN} v = bodyM -- ``f'' stands for the name of the function.

  progM :: defM1
           ...
           defMN
-}

data StmtM e x where
  -- | Entry point to a block.
  BlockEntry :: Name -- Name of the block
    -> Label    -- Label of the entry point.
    -> [Name] -- arguments
    -> StmtM C O

  -- | Entry point to a closure-capturing block.
  CloEntry :: Name -- Name of the block
    -> Label    -- Label of the entry point.
    -> [Name]   -- Variables in closure
    -> Name     -- argument
    -> StmtM C O
  
  Bind :: Name      -- Name of variable that will be bound.
    -> TailM    -- Expression that computes the value we want.
    -> StmtM O O    -- Open/open since bind does not end an expression
  
  CaseM :: Name      -- Variable to inspect
    -> [Alt TailM] -- Case arms
    -> StmtM O C
      
  Done :: TailM  -- Finish a block.
    -> StmtM O C

-- | TailM concludes a list of statements. Each block ends with a
-- TailM except when CaseM ends the blocks.
data TailM = Return Name 
  | Enter -- ^ Enter a closure.
    Name  -- ^ Variable holding the closure.
    Name  -- ^ Argument to the function.
  | Closure -- ^ Create a closure.
    Dest    -- ^ Label for the function held by the closure.
    [Name]  -- ^ List of captured free variables.
  | Goto   -- ^ Jump to a block.
    Dest   -- ^ Address of the block
    [Name] -- ^ Arguments/live variables used in the block.
  | ConstrM     -- ^ Create a data value.
    Constructor -- ^ Constructor name.
    [Name]      -- ^ Only variables allowed as arguments to
                -- constructor.
  | Thunk  -- ^ Monadic thunk - suspended computation.
    Dest   -- ^ Label of the computation's body.
    [Name] -- ^ Free variables in the body.
  | Run  -- ^ Execute a monadic computation.
    Name  -- ^ Variable holding the thunk


  deriving (Eq, Show)

-- Pretty printing programs
printStmtM :: StmtM e x -> Doc
printStmtM (Bind n b) = text n <+> text "<-" <+> nest 2 (printTailM b)
printStmtM (BlockEntry f l args) = text (show l ++ "_" ++ f) <+> 
                                  parens (commaSep text args) <> text ":" 
printStmtM (CloEntry f l clos arg) = text (show l ++ "_" ++ f) <+> 
                                  parens (text arg) <+> braces (commaSep text clos) <> text ":" 
printStmtM (CaseM v alts) = hang (text "case" <+> text v <+> text "of") 2 (vcat' $ map printAlt alts)
  where
    printAlt (Alt cons vs tailM) = text cons <+> hsep (texts vs) <+> text "->" <+> printTailM tailM
printStmtM (Done t) = printTailM t

printTailM :: TailM -> Doc
printTailM (Return n) = text "return" <+> text n
printTailM (Enter f a) = text f <+> text "@" <+> text a
printTailM (Closure dest vs) = text "closure" <+> printDest dest <+> braces (commaSep text vs)
printTailM (Goto dest vs) = printDest dest <> parens (commaSep text vs)
printTailM (ConstrM cons vs) = text cons <+> (hsep $ texts vs)

printDest :: Dest -> Doc
printDest (name, l) = text (show l ++ "_" ++ name)

instance NonLocal StmtM where
  entryLabel (BlockEntry _ l _) = l
  entryLabel (CloEntry _ l _ _) = l
  successors = stmtSuccessors
                        
stmtSuccessors :: StmtM e C -> [Label]
stmtSuccessors (CaseM _ alts) = map snd (concatMap (\(Alt _ _ t) -> tailDest t) alts)
stmtSuccessors (Done t) = map snd (tailDest t)

tailDest :: TailM -> [Dest]
tailDest (Closure dest _) = [dest]
tailDest (Goto dest _) = [dest]
tailDest _ = []
