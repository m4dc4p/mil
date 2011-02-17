{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module LCM

where

import Compiler.Hoopl
import Data.Set (Set)
import qualified Data.Set as Set

import Util
import MIL

-- | Anticipated expressions will always be some sort of tail: Enter,
-- Closure, Thunk, ConstrM or Return.  
--
-- Prim cannot be anticipated because we don't konw what side-effect
-- one might have. It doesn't make sense to anticipate Goto or Run
-- because they may also have side effects.
--
-- We index by the arguments used so we can tell when to remove
-- an expression. At the entry point to a block, the anticipated
-- expressions are all those tails whose arguments were not modified
-- during the course of the analysis. 
--
-- We will need to deal with how arguments are renamed between blocks
-- but not yet.
newtype AntFact = AF ((Used, Killed)
                     , Anticipated)

type Anticipated = (Env, Set TailM)

-- | Used expressions appear in the block but
-- their operands are not defined there.
type Used = Set TailM

-- | Killed expressions are defined in the block
-- or have operands defined there.
type Killed = Set TailM
type Env = [Name]

-- We will determine available expressions within 
-- a block by inspecting all tails and tracking the
-- arguments used. If those arguments are unchanged on
-- entry to the block, then the expression will be added
-- to the set of anticipated expressions for that block.
anticipateTransfer :: BwdTransfer StmtM AntFact
anticipateTransfer = mkBTransfer anticipate
  where
    anticipate :: StmtM e x -> Fact x AntFact -> AntFact
    anticipate (Bind v t) f = kill v (useExpr t f)
    anticipate (BlockEntry _ _ args) f = mkAnticipated f args
    anticipate (CloEntry _ _ args arg) f = mkAnticipated f (args++[arg])
    anticipate (Done t) f = fromSucc t f (renameExprs t)
    anticipate (CaseM v alts) f = 
      let antAlt (Alt _ vs t) = kills (fromSucc t f (useExpr t . renameExprs t)) vs 
      in unionFacts (map antAlt alts)

    -- | Get anticpated expression facts from our successor, if 
    -- there is one.
    fromSucc :: TailM -> FactBase AntFact -> (AntFact -> AntFact) -> AntFact
    fromSucc t facts f = maybe emptyFact f (lookupTail t facts)

    -- | Kill expressions that use the argument
    kill :: Name -> AntFact -> AntFact
    kill = undefined

    kills :: AntFact -> [Name] -> AntFact
    kills = foldr kill

    -- | Add the tail to the used expression list.
    useExpr :: TailM -> AntFact -> AntFact
    useExpr = undefined

    -- | Fix up final Anticipated value on exit
    -- from the block. Compute (Used `union` Killed) and
    -- add arguments environment for other blocks to rename with.
    mkAnticipated :: AntFact -> Env -> AntFact
    mkAnticipated = undefined

    unionFacts :: [AntFact] -> AntFact
    unionFacts = undefined

    -- | Replace variable names in anticipated expressions
    -- from successor with argument names used in this block,
    -- if the tail is a Goto or Closure. Otherwise, leave
    -- the facts given alone.
    renameExprs :: TailM -> AntFact -> AntFact
    renameExprs = undefined

     -- | Initial fact - no info.
    emptyFact :: AntFact
    emptyFact = undefined

    -- | Finds the facts for a particular case arm, if the 
    -- tail is a Goto or Closure. 
    lookupTail :: TailM -> FactBase AntFact -> Maybe AntFact
    lookupTail t f = undefined