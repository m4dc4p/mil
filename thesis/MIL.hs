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
  | Prim    -- ^ Execute a primitive block 
    Name    -- ^ Name of the primitive
    [Name]  -- ^ Arguments to the primitive


  deriving (Eq, Show)

-- Pretty printing programs
printStmtM :: StmtM e x -> Doc
printStmtM (Bind n b) = text n <+> text "<-" <+> nest 2 (printTailM b)
printStmtM (BlockEntry f _ args) = text f <+> 
                                  parens (commaSep text args) <> text ":" 
printStmtM (CloEntry f _ clos arg) = text f <+> 
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
printTailM (Thunk dest vs) = text "thunk" <+> printDest dest <+> brackets (commaSep text vs)
printTailM (Run v) = text "invoke" <+> text v
printTailM (Prim p vs) = text p <> text "*" <> parens (commaSep text vs)

printDest :: Dest -> Doc
printDest (name, _) = text name

printProgM :: ProgM C C -> Doc
printProgM = vcat' . maybeGraphCC empty printBlockM

printBlockM = p . blockToNodeList'
  where p (e, bs, x) = hang (maybeC empty printStmtM e) 2
                       (vcat' (map printStmtM bs) $+$
                        maybeC empty printStmtM x)
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

-- Primitives

primNames :: [Name]
primNames = map fst p
  where
    p :: [(Name, SimpleUniqueMonad (ProgM C C))]
    p = prims

prims :: UniqueMonad m => [(Name, m (ProgM C C))]
prims = [plusPrim
        , minusPrim
        , timesPrim
        , divPrim
        , ltPrim
        , gtPrim
        , ltePrim
        , gtePrim
        , eqPrim
        , neqPrim ]

plusPrim, minusPrim, timesPrim, divPrim, ltPrim, gtPrim, ltePrim, gtePrim, eqPrim, neqPrim :: UniqueMonad m => (Name, m (ProgM C C))

plusPrim = ("plus", binPrim "plus")
minusPrim = ("minus", binPrim "minus")
timesPrim = ("times", binPrim "times")
divPrim = ("div", binPrim "div")

ltPrim = ("lt", binPrim "lt")
gtPrim = ("gt", binPrim "gt")
ltePrim = ("lte", binPrim "lte")
gtePrim = ("gte", binPrim "gte")
eqPrim = ("eq", binPrim "eq")
neqPrim = ("neq", binPrim "neq")
                   
binPrim :: UniqueMonad m => Name -> m (ProgM C C)
binPrim name = do
  bodyLabel <- freshLabel
  c2Label <- freshLabel
  c1Label <- freshLabel
  let bodyName = name ++ "Body" 
      body = mkFirst (BlockEntry bodyName bodyLabel ["a", "b"]) <*>
             mkLast (Done $ Prim name ["a", "b"])
      c2Name = name ++ "Clo2"
      c2 = mkFirst (CloEntry c2Name c2Label ["a"] "b") <*>
           mkLast (Done $ Goto (bodyName, bodyLabel) ["a", "b"])
      c1 = mkFirst (CloEntry name c1Label [] "a") <*>
           mkLast (Done $ Closure (c2Name, c2Label) ["a"])
  return (c1 |*><*| c2 |*><*| body)