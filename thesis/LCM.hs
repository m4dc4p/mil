{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module LCM

where

import Data.Map (Map, (!))
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
    ant = anticipated (used body) (killed body) body

-- | Sets of Tail values.
type Exprs = Set Tail

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

postTransfer :: Earliest -> Used -> FwdTransfer Stmt PostFact
postTransfer early used = mkFTransfer fw
  where
    fw :: Stmt e x -> PostFact -> Fact x PostFact
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

availTransfer :: Anticipated -> FwdTransfer Stmt AvailFact
availTransfer ant = mkFTransfer fw
  where
    fw :: Stmt e x -> AvailFact -> Fact x AvailFact
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

    mkAvailable :: AvailFact -> Tail -> AvailFact
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
data AntFact = AF { afEnv :: Env
                  , afAnt :: Exprs {- anticipated -} }
  deriving (Eq)

anticipated :: Used -> Killed -> ProgM C C -> Anticipated
anticipated used killed body = runSimple $ do
    (_, f, _) <- analyzeAndRewriteBwd bwd (JustC (entryLabels body)) body mapEmpty
    return $ foldr mk Map.empty (mapToList f)
  where
    mk (l, (AF _ a)) ant = 
      let d = fromJust (labelToDest body l)
      in Map.insert d a ant
    bwd = BwdPass { bp_lattice = antLattice
                  , bp_transfer = antTransfer used killed
                  , bp_rewrite = noBwdRewrite } 

antLattice :: DataflowLattice AntFact
antLattice = DataflowLattice { fact_name = "Anticipated/available expressions"
                             , fact_bot = emptyAntFact
                             , fact_join = extend }
  where
    extend _ (OldFact old) (NewFact new) = (changeIf (old /= new), new)

-- | Initial anticipated expressions. 
emptyAntFact :: AntFact
emptyAntFact = AF [] {- args passed to block -}
                  Set.empty {- anticipated exprs -}

antTransfer :: Used -> Killed -> BwdTransfer Stmt AntFact
antTransfer uses kills = mkBTransfer anticipate
  where
    anticipate :: Stmt e x -> Fact x AntFact -> AntFact
    anticipate (BlockEntry n l args) f = mkAnticipated (n, l) f args
    anticipate (CloEntry n l args arg) f = mkAnticipated (n, l) f (args++[arg])

    anticipate (Bind _ _) f = f

    anticipate (CaseM _ alts) f = 
      let tails = [(l, args) | (Alt _ _ (Goto (_, l) args)) <- alts]
      in AF [] (Set.unions . map (fromSucc f) $ tails)
    anticipate (Done _ _ (Goto (_, l) args)) f = AF [] (fromSucc f (l, args))
    anticipate (Done _ _ _) _ = emptyAntFact

    -- | Get anticpated expression facts from our successor, if 
    -- any. Rename those facts to match local names as well.
    fromSucc :: FactBase AntFact -> (Label, Env) -> Exprs
    fromSucc facts (l, env) = 
      let succExprs (AF succEnv ant) = renameFact (mkRenamer env succEnv) ant
      in maybe Set.empty succExprs (lookupFact l facts)

    -- | Fix up final Anticipated value on exit from the
    -- block. 
    mkAnticipated :: Dest -> AntFact -> Env -> AntFact
    mkAnticipated dest (AF _ ant) env = 
      AF env ((uses ! dest) `Set.union` (ant `Set.difference` (kills ! dest)))

    -- | Rename anticipatable facts.
    renameFact :: (Name -> Name) -> Exprs -> Exprs
    renameFact r ants = renameTails r ants

    -- | Rename set of tail expressions.
    renameTails :: (Name -> Name) -> Exprs -> Exprs
    renameTails rename = Set.map (renameTail rename)

-- | If the tail gives a successor (i.e., a goto),
-- pair the destination with the value given. Otherwise,
-- return Nothing.
tailSucc :: Tail -> a -> Maybe (Label, a)
tailSucc t@(Goto (n, l) _) v = Just (l, v)
tailSucc _ _ = Nothing

intersections :: Ord a => [Set a] -> Set a
intersections [] = Set.empty
intersections xs = foldr1 Set.intersection xs

instance Show AntFact where
  show = showAnt

showAnt :: AntFact -> String
showAnt (AF env ant) = "(" ++ show env ++ ", " ++ 
                                  show (Set.elems ant) ++ ")"

-- | This defines the expressions we consider for LCM.
useable (Enter {}) = True
useable (Closure {}) = True
useable (ConstrM {}) = True
useable (Thunk {}) = True
useable (Prim {}) = True
useable (LitM {}) = True
useable _ = False

botUnion :: WithBot Exprs -> Exprs -> WithBot Exprs
botUnion Bot s = Bot
botUnion (PElem s) s' = PElem (Set.union s s')

botIntersect :: WithBot Exprs -> Exprs -> WithBot Exprs
botIntersect Bot s = PElem s
botIntersect (PElem s) s' = PElem (Set.intersection s s')

-- | Compute expressions used in each block.
used :: ProgM C C -> Map Dest Exprs
used = Map.fromListWith Set.union . map destUses . allBlocks
  where
    destUses :: (Dest, Block Stmt C C) -> (Dest, Exprs)
    destUses (dest, block) = (dest, foldFwdBlock uses Set.empty block)
                             
    uses :: forall e x. Exprs -> Stmt e x -> Exprs
    uses u (BlockEntry {}) = u
    uses u (CloEntry {}) = u
    uses u (Bind _ t) = Set.insert t u
    uses u (CaseM {}) = u
    uses u (Done n l t) = Set.insert t u 

-- | Compute expressions killed in each block.
killed :: ProgM C C -> Map Dest Exprs
killed = Map.fromListWith Set.union . map destKills . allBlocks
  where
    destKills :: (Dest, Block Stmt C C) -> (Dest, Exprs)
    destKills (dest, block) = 
      let (killed, _) = foldBwdBlock kills (Set.empty, Map.empty) block
      in (dest, killed)

    kills :: forall e x. Stmt e x -> (Exprs, Map Name Exprs) -> (Exprs, Map Name Exprs)
    kills (BlockEntry {}) (k, u) = (k, u)
    kills (CloEntry {}) (k, u) = (k, u)
    kills (Bind v t) (k, u) = 
      let updatedUses = Map.delete v u
      in (k `Set.union` Map.findWithDefault Set.empty v u
         , newUses t updatedUses)
    kills (CaseM {}) (k, u) = (k, u)
    kills (Done n l t) (k, u) = (k, newUses t u)

    newUses t old = 
      let new = Map.fromList $ zip (vars t) (repeat $ Set.singleton t)
      in Map.unionWith Set.union new old

