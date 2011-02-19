{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module LCM

where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromJust)

import Compiler.Hoopl

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
  deriving (Eq)

instance Show AntFact where
  show = showAnt

showAnt :: AntFact -> String
showAnt (AF (_, (env, ant))) = "(" ++ show env ++ ", " ++ 
                                  show (Set.elems ant) ++ ")"

type Anticipated = (Env, Set TailM)

-- | Used expressions appear in the block but
-- their operands are not defined there.
type Used = Set TailM

-- | Killed expressions are defined in the block
-- or have operands defined there.
type Killed = Set TailM
type Env = [Name]

anticipated :: ProgM C C -> [(Dest, AntFact)]
anticipated body = runSimple $ do
    (p, f, _) <- analyzeAndRewriteBwd bwd (JustC (entryLabels body)) body mapEmpty
    return $ map (\(l, fact) -> (fromJust (labelToDest body l), fact)) (mapToList f)
  where
    bwd = BwdPass { bp_lattice = antLattice
                  , bp_transfer = antTransfer 
                  , bp_rewrite = noBwdRewrite } 

antLattice :: DataflowLattice AntFact
antLattice = DataflowLattice { fact_name = "Anticipated expressions"
                             , fact_bot = emptyAntFact 
                             , fact_join = extend }
  where
    extend _ (OldFact old) (NewFact new) = (changeIf (old /= new)
                                           , new)

-- | Initial fact - no info.
emptyAntFact :: AntFact
emptyAntFact = AF ((Set.empty, Set.empty), ([], Set.empty))

-- We will determine available expressions within 
-- a block by inspecting all tails and tracking the
-- arguments used. If those arguments are unchanged on
-- entry to the block, then the expression will be added
-- to the set of anticipated expressions for that block.
--
-- New expressions defined in the block (which 
antTransfer :: BwdTransfer StmtM AntFact
antTransfer = mkBTransfer anticipate
  where
    anticipate :: StmtM e x -> Fact x AntFact -> AntFact
    anticipate (Bind v t) f = kill v (useExpr t f)
    anticipate (BlockEntry _ _ args) f = mkAnticipated f args
    anticipate (CloEntry _ _ args arg) f = mkAnticipated f (args++[arg])
    anticipate (Done t) f = useExpr t emptyAntFact -- fromSucc t f (renameExprs t)
    anticipate (CaseM v alts) f = emptyAntFact
{-      let antAlt (Alt _ vs t) = kills (fromSucc t f (useExpr t . renameExprs t)) vs 
      in unionFacts (map antAlt alts)
-}
    -- | Get anticpated expression facts from our successor, if 
    -- there is one.
    fromSucc :: TailM -> FactBase AntFact -> (AntFact -> AntFact) -> AntFact
    fromSucc t facts f = maybe emptyAntFact f (lookupTail t facts)

    -- | Kill expressions that use the argument
    kill :: Name -> AntFact -> AntFact
    kill v (AF ((used, killed), ant)) = 
      -- "uses" is more general than necessary since not
      -- all Tail instructions will appear in the
      -- use/kill sets.
      let toKill = Set.filter (uses v) used
      in AF ((used, killed `Set.union` toKill), ant)

    kills :: AntFact -> [Name] -> AntFact
    kills = foldr kill

    -- | True if the tail uses the name given.
    uses :: Name -> TailM -> Bool
    uses v t = v `elem` names t

    -- | Extract variable names from a tail.
    names :: TailM -> [Name]
    names (Enter f x) = [f, x]
    names (Closure _ vs) = vs
    names (Goto _ vs) = vs
    names (ConstrM _ vs) = vs
    names (Thunk _ vs) = vs
    names (Run v) = [v]
    names (Prim _ vs) = vs

    -- | Add the tail to the used expression list.
    useExpr :: TailM -> AntFact -> AntFact
    -- The following tails should not be considered
    -- for LCM, so we don't even add them to the used 
    -- set.
    useExpr (Goto _ _) f = f
    useExpr (Run _) f = f
    useExpr (Prim _ _) f = f
    useExpr (Return _) f = f
    useExpr t (AF ((used, killed), ant)) = 
      AF ((Set.insert t used, killed), ant)

    -- | Fix up final Anticipated value on exit
    -- from the block. Compute (Used `union` Killed) and
    -- add arguments environment for other blocks to rename with.
    mkAnticipated :: AntFact -> Env -> AntFact
    mkAnticipated (AF ((used, killed), _)) env = 
      let ant = used `Set.difference` killed
      in AF ((used, killed), (env, ant))

    unionFacts :: [AntFact] -> AntFact
    unionFacts = undefined

    -- | Replace variable names in anticipated expressions
    -- from successor with argument names used in this block,
    -- if the tail is a Goto or Closure. Otherwise, leave
    -- the facts given alone.
    renameExprs :: TailM -> AntFact -> AntFact
    renameExprs = undefined

    -- | Finds the facts for a particular case arm, if the 
    -- tail is a Goto or Closure. 
    lookupTail :: TailM -> FactBase AntFact -> Maybe AntFact
    lookupTail t f = undefined

