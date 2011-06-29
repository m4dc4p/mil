{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module LCM

where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe
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

-- | Anticipated expressions will be calculated on all subsequent
-- execution paths. Expressions here will be anticipated on entry to
-- the block (which also implies on exit).
type Anticipated = Map Dest Exprs

-- | Shows which expressions would be placed at the 
-- beginning of each block, if expressions were computed
-- as early as possible (i.e,  the "earliest placement"
-- strategy).
type Earliest = Map Dest Exprs

-- | Expressions available on entry
-- to the destination. These expressions will have
-- been computed when the block is entered. Expressions
-- computed IN the block are available to its successors,
-- but are not available in the block itself.
type Available = Map Dest Exprs

-- | For each block, gives the expressions which
-- can be postponed to the entry of the block.
type Postponable = Map Dest Exprs

-- | Gives the expressions that can be placed 
-- in each block using the "latest" (laziest) placement
-- strategy.
type Latest = Map Dest Exprs

-- | Gives all successors (immediate and beyond)
-- for each block.
type Successors = Map Dest (Set Dest)

type Env = [Name]
type Exprs = Set TailM

newtype PostFact = PP (Exprs {- used -}
                      , Exprs {- postponable -})
  deriving (Eq, Show)

latest :: Earliest -> Postponable -> Used -> Successors -> Latest
latest early post used succ =
    let -- Get the set of expressions to consider. By definition of
        -- latest, expression must be a member of earliest or postponable
        -- for the block, so we collect all those up.
        candidates :: [(Dest, Exprs)]
        candidates = filter (not . Set.null . snd) . map (\d -> (d, ep d)) $ nub (Map.keys early ++ Map.keys post)
    in Map.fromList $ map mkLatest candidates
  where
    -- | Create the latest set for the given block. The map returned
    -- always has one key but this makes it easier to combine all the
    -- maps above.
    mkLatest :: (Dest, Exprs) -> (Dest, Exprs)
    mkLatest (block, exprs) = 
      let qualifies expr = expr `Set.member` ep block && 
                           (expr `Set.member` usedBy block || 
                                 not (expr `Set.member` allSucc block))
      in (block, Set.filter qualifies exprs)
    -- | Expressions in earliest and postponable sets for
    -- the block.
    ep :: Dest -> Exprs
    ep block = lk early block `Set.union` lk post block
    -- | Expressions used by the given block.
    usedBy :: Dest -> Exprs
    usedBy block = lk used block
    -- | Lookup a set in the map. If the destination given
    -- is not in the map, return the empty set.
    lk :: Map Dest (Set a) -> Dest -> Set a 
    lk m d = fromMaybe Set.empty (Map.lookup d m) 
    -- | Return all expressions in all successors of the block
    allSucc :: Dest -> Exprs
    allSucc block = Set.unions (Set.elems (Set.map ep (lk succ block)))

postponable :: Earliest -> Used -> ProgM C C -> Postponable
postponable early used body = runSimple $ do
    (_, f, _) <- analyzeAndRewriteFwd fwd (JustC entryPoints) body initial
    return $ foldr mk Map.empty (mapToList f)
  where
    entryPoints = entryLabels body
    initial = mapFromList $ map mkInitialFact entryPoints 
    mkInitialFact l = 
      let dest = fromJust (labelToDest body l)
          use = fromMaybe Set.empty (Map.lookup dest used)
      in (l, PP (use, Set.empty))
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
    fw (CaseM _ alts) (PP (use, post)) = 
      let altT (Alt _ _ t) = tailSucc t post
          (labels, posts) = unzip . catMaybes $ map altT alts
          fact = PP (Set.empty, intersections posts)
      in mapFromList (zip labels (repeat fact))
    fw (Done _ _ t) (PP (use, post)) = 
      let (labels, facts) = unzip $ maybeToList (tailSucc t post)
      in mapFromList (zip labels (map (\f -> PP (Set.empty, f)) facts))

    mkInitial :: Dest -> PostFact -> PostFact
    mkInitial dest (PP (use, post)) =
      let use = fromMaybe Set.empty (Map.lookup dest used)
          ea = fromMaybe Set.empty (Map.lookup dest early)
      in PP (use, Set.difference (Set.union ea post) use)


-- | Expressions which are used in a block but
-- not killed. 
newtype AvailFact = AV (Exprs {- killed in this block. Used only during transfer analysis. -}
                       , Exprs {- available -})
  deriving (Eq, Show)

-- | Calculate earliest placement for each expression, if
-- there is an earlier placement.
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
          fact = case Map.lookup dest killed  of
                   Just k -> AV (k, Set.empty)
                   _ -> emptyAvailFact
      in (l, fact)
    mk (l, AV (_, av)) available = 
      let d = fromJust (labelToDest body l)
      in Map.insert d av available
    fwd = FwdPass { fp_lattice = availLattice
                  , fp_transfer = availTransfer antp
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

availTransfer :: Anticipated -> FwdTransfer StmtM AvailFact
availTransfer ant = mkFTransfer fw
  where
    fw :: StmtM e x -> AvailFact -> Fact x AvailFact
    fw (BlockEntry n l _) av = mkInitial (n,l) av
    fw (CloEntry n l _ _) av = mkInitial (n,l) av
    fw (Bind _ t) av = mkAvailable av t
    fw (CaseM _ alts) (AV (kill, avail)) = 
      let altT (Alt _ _ t) = tailSucc t avail
          (labels, avails) = unzip . catMaybes $ map altT alts
          fact = AV (kill, intersections avails)
      in mapFromList (zip labels (repeat fact))
    fw (Done _ _ t) av = mapFromList . maybeToList $ tailSucc t av
                     
    mkInitial :: Dest -> AvailFact -> AvailFact
    mkInitial (n, l) (AV (k, avIn)) = 
      let antIn = fromMaybe Set.empty (Map.lookup (n,l) ant)
      in AV (k, Set.difference (Set.union avIn antIn) k)

    mkAvailable :: AvailFact -> TailM -> AvailFact
    mkAvailable av@(AV (kill, avail)) t 
      | not (useable t) = av
      | otherwise = if t `Set.member` kill
                    then AV (kill, Set.delete t avail)
                    else AV (kill, Set.insert t avail)

-- | Anticipated expressions will always be some sort of tail: Enter,
-- Closure, ConstrM, Thunk, Prim or LitM.  
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
emptyAntFact = AF ((Set.empty {- used -}
                   , Set.empty {- killed -})
                  ,([] {- args passed to block -}
                   , Set.empty {- anticipated exprs -}))

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
    anticipate (Done _ _ t) f = use t (fromSucc t f)
    anticipate (CaseM v alts) f =
      let antAlt (Alt _ vs t) = kills (use t (fromSucc t f)) vs
      in intersectFacts (map antAlt alts)

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

    intersectFacts :: [AntFact] -> AntFact
    intersectFacts [] = emptyAntFact
    intersectFacts fs = foldr1 intersect fs
      where
        intersect (AF ((_, _), (_, ant1))) (AF ((_, _), (_, ant2))) =
          AF ((Set.empty, Set.empty), ([], ant1 `Set.intersection` ant2))

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

-- | If the tail gives a successor (i.e., a goto),
-- pair the destination with the value given. Otherwise,
-- return Nothing.
tailSucc :: TailM -> a -> Maybe (Label, a)
tailSucc t@(Goto (n, l) _) v = Just (l, v)
tailSucc _ _ = Nothing

intersections :: Ord a => [Set a] -> Set a
intersections [] = Set.empty
intersections xs = foldr1 Set.intersection xs

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
