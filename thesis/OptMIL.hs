{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module OptMIL (mostOpt, addLive, LiveFact
              , getEntryLabel, findLive, deadCode)

where

import Control.Monad.State (State, execState, modify, gets)
import Text.PrettyPrint 
import Data.List (sort, (\\), elemIndex)
import Data.Maybe (fromMaybe, isJust, catMaybes, fromJust)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace

import Compiler.Hoopl

import Util
import MIL
import Live
import DeadBlocks
import BindReturnElim
import Uncurry
import InlineReturn

-- From mon5.lhs
--   v <- return w; c  
--        ==>  c       if v == w
--        ==> [w/v] c  otherwise 
--
-- in Hoopl/MIL terms:
--
--   Bind v (Return w) <*> c  
--        ==> c    if v==w
--        ==> [w/v] c  otherwise
--

-- | Associates a binding (the key) with the
-- value that should be substituted for it. 
type BindFact = Map Name Tail

-- | Find "useless" bindings and remove them. Useless bindings 
-- include:
--
--   * bindings which return a value (x <- return y; c ==> [x/y] c)
--   * bindings which are followed by a return. (x <- y; return x ==> y)
--
-- This function really does two separate optimizations (eliminating
-- tails & removing useless binds) that should be separate.
bindSubst :: ProgM C C -> ProgM C C
bindSubst body = runSimple $ do
      let entries = entryLabels body
          initial :: FactBase BindFact
          initial = mapFromList (zip entries (repeat Map.empty))
      (p, _, _) <- analyzeAndRewriteFwd fwd (JustC entries) body initial
      return p
  where
    fwd :: FwdPass SimpleFuelMonad Stmt BindFact
    fwd = FwdPass { fp_lattice = bindSubstLattice
                  , fp_transfer = bindSubstTransfer
                  , fp_rewrite = bindSubstRewrite }

bindSubstLattice :: DataflowLattice BindFact
bindSubstLattice = DataflowLattice { fact_name = "Bind/Return substitution"
                                   , fact_bot = Map.empty
                                   , fact_join = extend }
  where
    extend _ (OldFact old) (NewFact new) = (changeIf (old /= new)
                                           , new)

bindSubstTransfer :: FwdTransfer Stmt BindFact
bindSubstTransfer = mkFTransfer fw
  where
    fw :: Stmt e x -> BindFact -> Fact x BindFact
    fw (Bind v t@(Return {})) m = Map.insert v t m 
    fw (Bind v t@(Closure {})) m = Map.insert v t m 
    fw (Bind v t@(Constr {})) m = Map.insert v t m 
    fw (Bind v t@(Thunk {})) m = Map.insert v t m 
    -- Why is LitM treated special here?
    fw (Bind v (LitM {})) m = Map.delete v m
    fw (Bind v _) m = m
    fw (BlockEntry _ _ _) m = m
    fw (CloEntry _ _ _ _) m = m
    fw (Case _ alts) m = 
      mkFactBase bindSubstLattice []
    fw (Done _ _ t) m = 
      mkFactBase bindSubstLattice []

bindSubstRewrite :: FuelMonad m => FwdRewrite m Stmt BindFact
bindSubstRewrite = 
    -- deep rewriting used so all possible substitutions occur
    iterFwdRw (mkFRewrite rewrite) 
  where
    rewrite :: FuelMonad m => forall e x. Stmt e x -> BindFact -> m (Maybe (ProgM e x))
    rewrite (Bind v t) f 
      | Map.member v f = bind v (rewriteTail f t)
    rewrite (Case v alts) f 
        | maybe False isNameBind (Map.lookup v f) = _case (substName f v) Just alts
        | otherwise = _case v (replaceAlt f) alts
        where
          replaceAlt f (Alt c ns t) 
            | anyNamesIn f ns = Just $ substNames f ns (\ns -> Alt c ns t)
            | otherwise = maybe Nothing (Just . Alt c ns) (rewriteTail f t)
    rewrite (Done n l t) f = done n l (rewriteTail f t)
    rewrite _ _ = return Nothing

    rewriteTail :: BindFact -> Tail -> Maybe Tail
    rewriteTail f (Return v) = substReturn f v 
    rewriteTail f (Enter v w) 
      | anyNamesIn f [v,w] = Just $ substNames f [v, w] (\ [v,w] -> Enter v w)
    rewriteTail f (Closure d ns) 
      | anyNamesIn f ns = Just $ substNames f ns (\ns -> Closure d ns)
    rewriteTail f (Goto d ns) 
      | anyNamesIn f ns = Just $ substNames f ns (\ns -> Goto d ns)
    rewriteTail _ _ = Nothing

    substReturn :: BindFact -> Name -> Maybe Tail
    substReturn f v =
      case Map.lookup v f of
        (Just (Return n)) -> Just $ Return n
        (Just (Enter fn x)) -> Just $ substNames f [fn, x] (\ [fn, x] -> Enter fn x)
        (Just (Closure d ns)) -> Just $ substNames f ns (\ns -> Closure d ns)
        (Just (Goto d ns)) -> Just $ substNames f ns (\ns -> Goto d ns)
        (Just (Constr c ns)) -> Just $ substNames f ns (\vs -> Constr c ns)
        (Just (Thunk d ns)) -> Just $ substNames f ns (\ns -> Thunk d ns)
        -- (Just (BindRun n)) -> Just $ substNames f [n] (\ [n] -> Invoke n)
        (Just (Prim p vs)) -> Just $ substNames f vs (\vs -> Prim p vs)
        _ -> Nothing

    -- | Find the name to substitue for the one
    -- given, if any. Return the original name
    -- if no substitution applies.
    substName :: BindFact -> Name -> Name
    substName f v = case Map.lookup v f of
                      (Just (Return v')) -> v'
                      _ -> v

    -- | Rewrite the names given according to facts, if those
    -- facts rewrite names. Otherwise, return original names. Order
    -- of the names is preserved.
    substNames :: BindFact -> [Name] -> ([Name] -> a) -> a
    substNames f ns mkA = mkA (foldr doSubst [] ns)
      where
        doSubst v names = substName f v : names

    -- | Indicates if any of the names given
    -- have BindReturn substitutions.
    anyNamesIn :: BindFact -> [Name] -> Bool
    anyNamesIn f ns = any (\n -> maybe False isNameBind $ Map.lookup n f) ns

    isNameBind (Return _) = True
    isNameBind _ = False

printBindFacts :: FactBase BindFact -> Doc
printBindFacts = printFB printFact
  where
    printFact :: (Label, Map Name Tail) -> Doc
    printFact (l, ns) = text (show l) <> text ":" <+> commaSep (text . show) (Map.toList ns)

-- Implementing CC-Let (figure 6) from Kennedy's paper:
--
--   x2 <- (x1 <- A; B); C
-- ==>
--   x1 <- A; x2 <- B; C
--
-- This manifests as inlining in our language:
--
--   L2: x1 <- L1() -- L1 defines A, not shown.
--       ...
--       bN  -- L2 defines B.
--   L3: x2 <- L2()  
--       ...
--       cN   -- L3 defines C.
--
-- which we want to rewrite as:
-- 
--   L3: x1 <- L1()
--       ...
--       x2 <- bN -- If L2 consists only of x1 <- L1() then this statement
--                -- collapses to x2 <- L1() and x1 <- L1() disappears.
--       c1 
--       ...
--       cN
--
-- This program only inlines L2 when only one predecessor exists (i.e.,
-- it has only one caller).

-- Nothing -- unknown
-- Just True - will inline
-- Just False - will not inline
type InlineFact = Maybe Bool

inlineBlocks :: [Name] -> ProgM C C -> ProgM C C
inlineBlocks tops body = 
  case runInline tops body of
    (True, body') -> inlineBlocks tops body'
    (_, body') -> body'

runInline :: [Name] -> ProgM C C -> (Bool, ProgM C C)
runInline tops body = runSimple $ do
    (body', f, _) <- analyzeAndRewriteBwd bwd (JustC labels) body initial
    return (or (catMaybes (mapElems f)), body')
  where
    preds = findBlockReferrers body
    labels = entryLabels body
    initial = mkFactBase (bp_lattice bwd) (zip labels (repeat Nothing))
    bwd = BwdPass { bp_lattice = inlineLattice
                  , bp_transfer = inlineTransfer preds 
                  , bp_rewrite = inlineRewrite preds body }


inlineLattice :: DataflowLattice InlineFact
inlineLattice = DataflowLattice { fact_name = "Inline blocks"
                                , fact_bot = Nothing
                                , fact_join = extend }
  where
    extend _ (OldFact old) (NewFact new) = (changeIf (old /= new)
                                           , new)

inlineTransfer :: BlockReferrers -> BwdTransfer Stmt InlineFact
inlineTransfer referrers = mkBTransfer bw
  where
    -- Find blocks which are the sole referrer to another
    -- block. 
    bw :: Stmt e x -> Fact x InlineFact -> InlineFact
    bw (Bind v (Goto dest vs)) f = singlePred referrers dest f 
    bw (Bind {}) f = f
    bw (Case {}) _ = Just False
    bw (Done _ _ (Goto dest _)) f = Nothing -- singlePred preds dest Nothing
    bw (Done {}) _ = Nothing
    bw (CloEntry {}) f = f
    bw (BlockEntry {}) f = f

inlineRewrite :: FuelMonad m => BlockReferrers -> ProgM C C -> BwdRewrite m Stmt InlineFact
inlineRewrite referrers prog = mkBRewrite rewriter
  where
    rewriter :: FuelMonad m => forall e x. Stmt e x -> Fact x InlineFact -> m (Maybe (ProgM e x))
    rewriter (Bind v (Goto dest vs)) (Just True) = return (inlineBind v dest vs)
    rewriter (Done _ _ (Goto dest vs)) _ = 
      case singlePred referrers dest Nothing of
        Just True -> return (inlineDone dest vs)
        _ -> return Nothing

    rewriter _ _ = return Nothing

    inlineDone :: Dest -> [Name] -> Maybe (ProgM O C)
    inlineDone (_, l) args = Nothing -- not yet implemented

    inlineBind :: Name -> Dest -> [Name] -> Maybe (ProgM O O)
    inlineBind result (_, l) args = maybe Nothing (Just . snd . renameInBody . snd) (blockOfLabel prog l)
      where
          renameInBody body = foldGraphNodes rename  
                                             (blockTail body) 
                                             (mkEnv body, emptyGraph)
          -- Create a map from formal arguements
          -- to actual arguments so we can rename.
          mkEnv :: Block Stmt C C -> Map Name Name
          mkEnv body = Map.fromList (zip (entryArgs body) args)
          entryArgs :: Block Stmt C C -> [Name]
          entryArgs body = case blockEntry body of
                             BlockEntry  _ _ args -> args
                             CloEntry _ _ clo arg -> clo ++ [arg]
          rename :: forall e x. Stmt e x -> (Map Name Name, ProgM O O) -> (Map Name Name, ProgM O O)
          rename (Bind v tail) (env, prog) 
            | v `Map.member` env = (Map.delete v env, newProg)
            | otherwise = (env, newProg)
            where
              newProg = prog <*> mkMiddle (Bind v (changeTail env tail))
          rename (Done _ _ tail) (env, prog) = (env, prog <*> mkMiddle (Bind result (changeTail env tail)))
          changeTail :: Map Name Name -> Tail -> Tail
          changeTail env (Return n) = Return (changeVar env n)
          changeTail env (Enter f x) = Enter (changeVar env f) (changeVar env x)
          changeTail env (Closure dest vs) = Closure dest (map (changeVar env) vs)
          changeTail env (Goto dest vs) = Goto dest (map (changeVar env) vs)
          changeTail env (Constr c ns) = Constr c (map (changeVar env) ns)
          changeTail env (LitM i) = LitM i
          changeTail env (Thunk dest vs) = Thunk dest (map (changeVar env) vs)
          changeTail env (Invoke v) = Invoke (changeVar env v)
          changeTail env (Prim p vs) = Prim p (map (changeVar env) vs)
          changeVar env f = Map.findWithDefault f f env

singlePred :: BlockReferrers -> Dest -> InlineFact -> InlineFact
singlePred referrers dest f 
  | dest `Map.member` referrers && Set.size (referrers ! dest) == 1 = Just (maybe True (True &&) f)
  | otherwise = f

-- | Collapse closures, then elminate dead assignments
-- in blocks.
optCollapse tops = deadCode . collapse

mostOpt :: [Name] -> ([Name], ProgM C C) -> ProgM C C -> ProgM C C
mostOpt tops prelude@(prims, _) = id .
    -- deadBlocks tops . 
    -- inlineBlocks tops . 
    deadBlocks tops .  
    collapse . 
    inlineReturn .
    deadCode . 
    collapse . 
    deadCode . 
    bindSubst . 
    inlineReturn .
    collapse . 
    bindReturn . 
    deadCode . 
    bindSubst 

-- | Converts the names given to a set of Dest values. Any
-- names which do not have corresponding entry points in the program
-- given will not appear in the output set.
namesToDests :: [Name] -> ProgM C C -> Set Dest
namesToDests names = Set.fromList . filter (\(n, l) -> n `elem` names) . map fst . allBlocks