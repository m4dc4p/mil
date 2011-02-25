{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module LCM

where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromJust)
import Data.List (nub)

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
newtype AntFact = AF ((Used, Killed)
                     , Anticipated)
  deriving (Eq)

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
    anticipate (Bind v t) f = kill v (use t f)
    anticipate (BlockEntry _ _ args) f = mkAnticipated f args
    anticipate (CloEntry _ _ args arg) f = mkAnticipated f (args++[arg])
    anticipate (Done t) f = use t (fromSucc t f)
    anticipate (CaseM v alts) f =
      let antAlt (Alt _ vs t) = kills (use t (fromSucc t f)) vs
      in unionFacts (map antAlt alts)

    -- | Get anticpated expression facts from our successor, if 
    -- any. Rename those facts to match local names as well.
    fromSucc :: TailM -> FactBase AntFact -> AntFact
    fromSucc (Goto (_, l) args) facts = 
      let succFact f@(AF (_, (_, ants))) = renameFact (mkRenamer args f) f
      in maybe emptyAntFact succFact (lookupFact l facts)
    fromSucc _ _ = emptyAntFact

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
    use :: TailM -> AntFact -> AntFact
    -- The following tails should not be considered
    -- for LCM, so we don't even add them to the used 
    -- set.
    use (Goto _ _) f = f
    use (Run _) f = f
    use (Return _) f = f
    use t (AF ((used, killed), ant)) = 
      AF ((Set.insert t used, killed), ant)

    -- | Fix up final Anticipated value on exit from the
    -- block. Compute (Used `union` Killed), union with any existing
    -- anticipated expressions and add our environment for other
    -- blocks to rename with.
    mkAnticipated :: AntFact -> Env -> AntFact
    mkAnticipated (AF ((used, killed), (_, ant))) env = 
      AF ((used, killed)
         , (env, Set.union ant (used `Set.difference` killed)))

    unionFacts :: [AntFact] -> AntFact
    unionFacts [] = emptyAntFact
    unionFacts facts = foldr1 addFact facts
      where
        addFact :: AntFact -> AntFact -> AntFact
        addFact (AF ((uses1, kills1), (env1, ant1))) 
          (AF ((uses2, kills2), (env2, ant2))) = 
            AF ((uses1 `Set.union` uses2, kills1 `Set.union` kills2)
               ,([], ant1 `Set.intersection` ant2))

    -- | Create a function which will rename
    -- successor expressions and facts with
    -- the local block names. The renaming 
    -- function will return the name in this block
    -- or the original name, if no renaming occurred.
    mkRenamer :: Env -> AntFact -> (Name -> Name)
    mkRenamer env (AF (_, (succEnv, ant))) = 
      let succMap = Map.fromList (zip succEnv env)
      in \n -> maybe n id (Map.lookup n succMap)

    -- | Rename anticipatable facts.
    renameFact :: (Name -> Name) -> AntFact -> AntFact
    renameFact r (AF (_, (_, ants))) = AF ((Set.empty, Set.empty)
                                          ,([], renameTails r ants))

    -- | Rename set of tail expressions.
    renameTails :: (Name -> Name) -> Set TailM -> Set TailM
    renameTails rename = Set.map (renameTail rename)

    -- | Rename all variables used in anticipatable 
    -- tail expressions.
    renameTail :: (Name -> Name) -> TailM -> TailM
    renameTail r (Enter f x) = Enter (r f) (r x)
    renameTail r (Closure dest vs) = Closure dest (map r vs)
    renameTail r (ConstrM c vs) = ConstrM c (map r vs)
    renameTail r (Thunk dest vs) = Thunk dest (map r vs)
    renameTail r (Prim p vs) = Prim p (map r vs)
    -- Any other type of Tail expressions should not appear
    -- in the anticipated set we are renaming anyways.
    renameTail r t = t

instance Show AntFact where
  show = showAnt

showAnt :: AntFact -> String
showAnt (AF (_, (env, ant))) = "(" ++ show env ++ ", " ++ 
                                  show (Set.elems ant) ++ ")"

