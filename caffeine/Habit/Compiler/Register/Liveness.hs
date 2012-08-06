{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}
module Habit.Compiler.Register.Liveness

where

import Compiler.Hoopl
import Data.Maybe (fromMaybe)
import Data.Set (Set, (\\))
import qualified Data.Set as Set
import Data.List(foldl')

import qualified Habit.Compiler.Register.Machine as H (Reg, Instr(..))
import Habit.Compiler.Register.Hoopl

type LiveFact = Set H.Reg

liveOpt :: Body InstrNode -> FuelMonad (Body InstrNode)
liveOpt body = do
  let bwd = BwdPass { bp_lattice = liveLattice
                       , bp_transfer = liveTransfer 
                       , bp_rewrite = liveRewrite }
  (body', _) <- analyzeAndRewriteBwd bwd body (mkFactBase [])
  return body'

liveLattice :: DataflowLattice LiveFact
liveLattice = DataflowLattice { fact_name = "Liveness"
                              , fact_bot = Set.empty
                              , fact_extend = extend
                              , fact_do_logging = True }
  where
    extend _ (OldFact old) (NewFact new) = 
      let c = if Set.null(old \\ new) && Set.null (new \\ old)
              then NoChange
              else SomeChange
      in (c, old `Set.union` new)
                                         
{- | liveTransfer adds facts based on the type of node:

    Open/Closed: Transfer all live registers from target labels.
    Open/Open: Transfer all register that are live, remove any that are killed.
    Closed/Open: Return all registers that are known to be live now.

    Does this work for global registers allocated in TOP but only used elsewhere?
-}
liveTransfer :: BwdTransfer InstrNode LiveFact
liveTransfer (EntryLabel _ _ l) f = mkFactBase [(l, f)]
liveTransfer (LabelNode _ _ l) f = mkFactBase [(l, f)]
liveTransfer (CaptureLabel _ _ _ _ _ l) f = mkFactBase [(l, f)]
liveTransfer (Open (H.Enter src arg dest)) f = Set.insert src . Set.insert arg . Set.delete dest $ f
liveTransfer (Open (H.MkClo dest _ srcs)) f = foldl' update (Set.delete dest f) srcs
  where
    update set reg = Set.insert reg set
liveTransfer (Open (H.AllocD dest _ _)) f = Set.delete dest f
liveTransfer (Open (H.Copy _ dest)) f = Set.delete dest f
liveTransfer (Open (H.Store src (dest, _))) f = Set.insert src (Set.delete dest f)
liveTransfer (Open (H.Load (src,_) dest)) f = Set.insert src (Set.delete dest f)
liveTransfer (Open (H.Set dest _)) f = Set.delete dest f
liveTransfer (Open _) f = f
liveTransfer (Jmp _ l) f = fromMaybe Set.empty $ lookupFact f l
liveTransfer (FailT _ (F fl) (T tl)) f = fromMaybe Set.empty (lookupFact f tl) `Set.union`
                                               fromMaybe Set.empty (lookupFact f fl)
liveTransfer (Ret r) _ = Set.singleton r
liveTransfer (Capture r _ _ _) _ = Set.singleton r
liveTransfer (Error _) _ = Set.empty
liveTransfer (Halt _) _ = Set.empty

-- type BwdRewrite n f = forall e x. n e x -> Fact x f -> Maybe (BwdRes n f e x)
-- data BwdRes n f e x = BwdRes (AGraph n e x) (BwdRewrite n f)
liveRewrite :: BwdRewrite InstrNode LiveFact
liveRewrite = shallowBwdRw f
  where
    f :: SimpleBwdRewrite InstrNode LiveFact
    f (Open (H.Copy _ dest)) live 
            | dest `Set.member` live = Nothing
            | otherwise = Just emptyGraph
    f (Open (H.Load _ dest)) live 
            | dest `Set.member` live = Nothing
            | otherwise = Just emptyGraph
    f (Open (H.Enter _ _ dest)) live 
            | dest `Set.member` live = Nothing
            | otherwise = Just emptyGraph
    f (Open (H.MkClo dest _ _)) live 
            | dest `Set.member` live = Nothing
            | otherwise = Just emptyGraph
    f _ _ = Nothing
                                               