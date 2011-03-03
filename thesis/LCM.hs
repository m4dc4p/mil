{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module LCM

where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromJust, catMaybes, maybeToList)
import Data.List (nub)

import Compiler.Hoopl

import Util
import MIL

lcm :: ProgM C C -> ProgM C C
lcm body = undefined
  where
    (used, killed, ant) = anticipated body

-- | Used expressions appear in the block but
-- their operands are not defined there.
type Used = Map Dest Exprs

-- | Killed expressions are defined in the block
-- or have operands defined there.
type Killed = Map Dest Exprs

-- | Anticipated expressions will be calculated
-- on all subsequent execution paths.
type Anticipated = Map Dest Exprs

-- | The entries for each destination are the earliest
-- points at which those expressions are available.
type Earliest = Map Dest Exprs

-- | Available expressions are anticipated 
-- or defined in the block and not killed.
type Available = Map Dest Exprs

-- | For each block, gives the expressions which
-- can be postponed to the entry of the block.
type Postponable = Map Dest Exprs

type Env = [Name]
type Exprs = Set TailM

newtype PostFact = PP (Exprs {- used -}
                      , Exprs {- postponable -})
  deriving (Eq, Show)

postponable :: Earliest -> Used -> ProgM C C -> Postponable
postponable early used body = runSimple $ do
    (_, f, _) <- analyzeAndRewriteFwd fwd (JustC entryPoints) body initial
    return $ foldr mk Map.empty (mapToList f)
  where
    entryPoints = entryLabels body
    initial = mapFromList $ map mkInitialFact entryPoints 
    mkInitialFact l = 
      let dest = fromJust (labelToDest body l)
          fact = case (Map.lookup dest used, Map.lookup dest early) of
                   (Just use, Just ea) -> PP (use, Set.difference ea use)
                   (Just use, _) -> PP (use, Set.empty)
                   (_, Just ea) -> PP (Set.empty, ea)
                   _ -> emptyPostFact
      in (l, fact)
    mk (l, PP (_, pp)) postponable = 
      let d = fromJust (labelToDest body l)
      in Map.insert d pp postponable
    fwd = FwdPass { fp_lattice = postLattice
                  , fp_transfer = postTransfer early used
                  , fp_rewrite = noFwdRewrite }

emptyPostFact :: PostFact
emptyPostFact = PP (Set.empty, Set.empty)

postLattice :: DataflowLattice PostFact
postLattice = DataflowLattice { fact_name = "Postponable expressions"
                              , fact_bot = emptyPostFact
                              , fact_join = extend }
  where
    extend _ (OldFact old@(PP (_, oldPp))) (NewFact new@(PP (_, newPp))) = 
      (changeIf (oldPp `Set.isProperSubsetOf` newPp), new)

postTransfer :: Earliest -> Used -> FwdTransfer StmtM PostFact
postTransfer early used = mkFTransfer fw
  where
    fw :: StmtM e x -> PostFact -> Fact x PostFact
    fw (BlockEntry n l _) pp = mkInitial (n, l) pp
    fw (CloEntry n l _ _) pp = mkInitial (n, l) pp
    fw (Bind _ t) pp@(PP (use, ea)) 
       | useable t && not (t `Set.member` use) = PP (use, Set.insert t ea)
       | otherwise = pp
    fw (CaseM _ alts) pp = 
      let altE (Alt _ _ t) = tailSucc t pp
      in foldr mapUnion mapEmpty (map altE alts)
    fw (Done t) pp = tailSucc t pp

    mkInitial :: Dest -> PostFact -> PostFact
    mkInitial dest (PP (_, post)) =
      let use = maybe Set.empty id (Map.lookup dest used)
          ea = maybe Set.empty id (Map.lookup dest early)
      in PP (use, Set.difference ea use)

    tailSucc :: TailM -> PostFact -> FactBase PostFact
    tailSucc t pp@(PP (use, ea)) =
      let labels = map snd (tailSuccessors t)
          facts = zip labels $
                  if useable t && not (t `Set.member` use) 
                  then repeat (PP (use, Set.insert t ea))
                  else repeat pp
      in mkFactBase postLattice facts

-- | Expressions which are used in a block but
-- not killed. 
newtype AvailFact = AV (Exprs {- killed -} 
                       , Exprs {- available -})
  deriving (Eq, Show)

earliest :: Anticipated -> Available -> Earliest
earliest antp avail = 
  let f :: Dest -> Exprs -> Exprs
      f dest antExprs = 
        case Map.lookup dest avail of
          Just availExprs -> Set.difference antExprs availExprs
          Nothing -> antExprs
  in Map.mapWithKey f antp

available :: Anticipated -> Killed -> ProgM C C -> Available
available antp killed body = runSimple $ do
    (_, f, _) <- analyzeAndRewriteFwd fwd (JustC entryPoints) body initial
    return $ foldr mk Map.empty (mapToList f)
  where
    entryPoints = entryLabels body
    initial = mapFromList $ map mkInitialFact entryPoints 
    -- Compute initial available expressions for each block. Our
    -- initial fact is the anticipated expressions in the block, minus
    -- any killed expressions.
    mkInitialFact l = 
      let dest = fromJust (labelToDest body l)
          fact = case (Map.lookup dest killed, Map.lookup dest antp)  of
                   (Just k, Just a) -> AV (k, Set.difference a k)
                   (Just k, _) -> AV (k, Set.empty)
                   (_, Just a) -> AV (Set.empty, a)
                   _ -> emptyAvailFact
      in (l, fact)
    mk (l, AV (_, av)) available = 
      let d = fromJust (labelToDest body l)
      in Map.insert d av available
    fwd = FwdPass { fp_lattice = availLattice
                  , fp_transfer = availTransfer 
                  , fp_rewrite = noFwdRewrite }

-- | Initial available expression fact.
emptyAvailFact :: AvailFact
emptyAvailFact = AV (Set.empty, Set.empty)

availLattice :: DataflowLattice AvailFact
availLattice =  DataflowLattice { fact_name = "Available expressions"
                                , fact_bot = emptyAvailFact 
                                , fact_join = extend }
  where
    extend _ (OldFact old@(AV (_, oldAv))) (NewFact new@(AV (_, newAv))) = 
      (changeIf (oldAv `Set.isProperSubsetOf` newAv), new)

availTransfer :: FwdTransfer StmtM AvailFact
availTransfer = mkFTransfer fw
  where
    fw :: StmtM e x -> AvailFact -> Fact x AvailFact
    fw (BlockEntry n l _) av = av
    fw (CloEntry n l _ _) av = av
    fw (Bind _ t) av = mkAvailable av t
    fw (CaseM _ alts) av@(AV (kill, _)) = 
      let altT (Alt _ _ t) = tailSucc t av
          (labels, avail) = unzip . catMaybes $ map altT alts
          intersections [] = Set.empty
          intersections [x] = x
          intersections xs = foldr1 Set.intersection xs
          fact = AV (kill, intersections $ map (\(AV (_, a)) -> a) avail)
      in mapFromList (zip labels (repeat fact))
    fw (Done t) av = mapFromList . maybeToList $ tailSucc t av

    mkAvailable :: AvailFact -> TailM -> AvailFact
    mkAvailable av@(AV (kill, avail)) t 
      | not (useable t) = av
      | otherwise = if t `Set.member` kill
                    then AV (kill, Set.delete t avail)
                    else AV (kill, Set.insert t avail)

    tailSucc :: TailM -> AvailFact -> Maybe (Label, AvailFact)
    tailSucc t@(Goto (n, l) _) av = Just (l, mkAvailable av t)
    tailSucc _ _ = Nothing

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
-- Environment helps with renaming across blocks but
-- is not used after the analysis has finished.
newtype AntFact = AF ((Exprs {- used -}, Exprs {- killed -})
                     , (Env, Exprs {- anticipated -}))
  deriving (Eq)

anticipated :: ProgM C C -> (Used, Killed, Anticipated)
anticipated body = runSimple $ do
    (_, f, _) <- analyzeAndRewriteBwd bwd (JustC (entryLabels body)) body mapEmpty
    return $ foldr mk (Map.empty, Map.empty, Map.empty) (mapToList f)
  where
    mk (l, AF ((u, k), (_, a))) (used, killed, ant) = 
      let d = fromJust (labelToDest body l)
      in (Map.insert d u used
         , Map.insert d k killed
         , Map.insert d a ant)
    bwd = BwdPass { bp_lattice = antLattice
                  , bp_transfer = antTransfer 
                  , bp_rewrite = noBwdRewrite } 

antLattice :: DataflowLattice AntFact
antLattice = DataflowLattice { fact_name = "Anticipated/available expressions"
                             , fact_bot = emptyAntFact
                             , fact_join = extend }
  where
    extend _ (OldFact old) (NewFact new) = (changeIf (old /= new), new)

-- | Initial anticipated expressions. 
emptyAntFact :: AntFact
emptyAntFact = AF ((Set.empty, Set.empty), ([], Set.empty))

-- We will determine available expressions within 
-- a block by inspecting all tails and tracking the
-- arguments used. If those arguments are unchanged on
-- entry to the block, then the expression will be added
-- to the set of anticipated expressions for that block.
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
    names _ = []

    -- | Add the tail to the used expression list.
    use :: TailM -> AntFact -> AntFact
    use t f@(AF ((used, killed), ant)) 
      | useable t = AF ((Set.insert t used, killed), ant)
      | otherwise = f

    -- | Fix up final Anticipated value on exit from the
    -- block. Compute (Used `union` Killed), union with any existing
    -- anticipated expressions and add our environment for other
    -- blocks to rename with.
    mkAnticipated :: AntFact -> Env -> AntFact
    mkAnticipated (AF ((used, killed), (_, ant))) env = 
      AF ((used, killed)
         , (env, Set.union ant (Set.difference used killed)))

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

-- | Availability -- find 

instance Show AntFact where
  show = showAnt

showAnt :: AntFact -> String
showAnt (AF (_, (env, ant))) = "(" ++ show env ++ ", " ++ 
                                  show (Set.elems ant) ++ ")"

-- | This defines the expressions we consider for LCM.
useable (Enter {}) = True
useable (Closure {}) = True
useable (ConstrM {}) = True
useable (Thunk {}) = True
useable (Prim {}) = True
useable (LitM {}) = True
useable _ = False
