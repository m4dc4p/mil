{-# LANGUAGE GADTs, RankNTypes #-}

import Compiler.Hoopl
import Data.Map (Map, (!))
import qualified Data.Map as Map

type Name = String
type Var = String
type Constructor = String
type Dest = (Name, Label)

data Alt e = Alt Constructor [Name] e
  deriving (Show, Eq)

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
      
  Done :: Name -- ^ Name of this block
    -> Label -- ^ Label of this block
    -> TailM  -- Finish a block.
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
  | Invoke  -- ^ Execute a monadic computation.
    Name  -- ^ Variable holding the thunk
  | Prim    -- ^ Execute a primitive block 
    Name    -- ^ Name of the primitive
    [Name]  -- ^ Arguments to the primitive
  | LitM    -- ^ Numeric value
    Integer 
  deriving (Eq, Ord, Show)


type CollapseFact = Map Name (WithTop CloVal) -- Need to track

collapseRewrite :: FuelMonad m => Map Label DestOf -> FwdRewrite m StmtM CollapseFact
collapseRewrite blocks = iterFwdRw (mkFRewrite rewriter)
  where
    rewriter :: FuelMonad m => forall e x. StmtM e x -> CollapseFact -> m (Maybe (ProgM e x))
    rewriter (Done n l (Enter f x)) col = done n l (collapse col f x)
    rewriter (Bind v (Enter f x)) col = bind v (collapse col f x)
    rewriter _ _ = return Nothing

    -- collapse :: CollapseFact -> Name -> Name -> Maybe TailM
    collapse col f x =       
      case Map.lookup f col of
        Just (PElem (CloVal dest@(_, l) vs)) -> -- Just (Closure dest (vs ++ [x]))
          case l `Map.lookup` blocks of
            Just (Jump dest) -> Just (Goto dest (vs ++ [x]))
            Just (Capture dest (Just idx)) -> Just (Closure dest (insertAt vs idx x))
            Just (Capture dest _) -> Just (Closure dest vs)
            _ -> Nothing
        _ -> Nothing

