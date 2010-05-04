{-# LANGUAGE GADTs, NamedFieldPuns  #-}
{-# OPTIONS_GHC -Wall #-}
module Habit.Compiler.Register.ClosureElimination (cloOpt)

where

import Compiler.Hoopl
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, fromJust, isJust)

import qualified Habit.Compiler.Register.Machine as H (Reg, Instr(..), Label)
import Habit.Compiler.Register.Hoopl

data CloInfo = MkClo H.Label Int | Other
  deriving (Eq, Show)

data CloFact = CloFact { currLabel :: Maybe (H.Label, Label) -- ^ Track currently being analyzed.
                       , closureRefs :: Map H.Reg CloInfo -- ^ Map the registers holding "constant" closures to those closures.
                       , allClosures :: Map H.Label CloInfo  } -- ^ Map program labels to the closures they make, if any. 
  deriving (Eq, Show)

emptyFact :: CloFact 
emptyFact = CloFact { currLabel = Nothing
                    , closureRefs = Map.empty
                    , allClosures = Map.empty }
            
cloOpt :: Body InstrNode -> FuelMonad (Body InstrNode)
cloOpt body = do
  let fwd = FwdPass { fp_lattice = cloLattice
                       , fp_transfer = cloTransfer 
                       , fp_rewrite = cloRewrite }
      -- Initial map of labels to initial facts.
      initFacts = zip (map fst (bodyList body)) (repeat emptyFact)
  (body', _) <- analyzeAndRewriteFwd fwd body (mkFactBase initFacts)
  return body'

cloLattice :: DataflowLattice CloFact
cloLattice = DataflowLattice { fact_name = "Closure elimination"
                              , fact_bot = emptyFact
                              , fact_extend = extendFact
                              , fact_do_logging = True }
  where
    extendFact _ (OldFact old@(CloFact _ oldRef oldAll)) (NewFact new@(CloFact _ newRef newAll)) 
      | oldRef == newRef && oldAll == newAll = (NoChange, old)
      | otherwise = let ref' = newRef `Map.union` oldRef
                        all' = newAll `Map.union` oldAll
                    in (SomeChange, new { closureRefs = ref'
                                        , allClosures = all' })
                                           

cloTransfer :: FwdTransfer InstrNode CloFact
-- Initialize analysis for this block when we see a label.
cloTransfer (EntryLabel (G l) _ hl) f = 
  let fact = fromMaybe emptyFact $ lookupFact f hl
  in fact { currLabel = Just (l, hl) } 
cloTransfer (LabelNode _ (N l) hl) f = 
  let fact = fromMaybe emptyFact $ lookupFact f hl
  in fact { currLabel = Just (l, hl) }

-- Add teh value of the result register to the map of labels to
-- closures. If a closure was allocated in this register, and it has
-- not been overwritten, then it will have the value MkClo. Otherwise,
-- it will the value Other.
cloTransfer (Ret (H.Ret _)) f@(CloFact { currLabel = Just (curr, hCurr)
                                       , closureRefs
                                       , allClosures }) 
  = case Map.lookup curr closureRefs of
      Just cloInfo@(MkClo _ _) -> mkFactBase [(hCurr, f { allClosures = Map.insert curr cloInfo allClosures })]
      _ -> mkFactBase []

cloTransfer (Open (H.MkClo reg _ regs)) f@(CloFact { closureRefs }) = 
  let cloInfo = MkClo reg (length regs)
  in f { closureRefs = Map.insert reg cloInfo closureRefs } 

-- Transfer our facts to target labels.
cloTransfer (Jmp _ hl) f@(CloFact { currLabel = Just (curr, hCurr)
                                  , closureRefs
                                  , allClosures }) 
  = case Map.lookup curr closureRefs of
      Just cloInfo@(MkClo _ _) -> 
        let newFact = f { allClosures = Map.insert curr cloInfo allClosures } 
        in mkFactBase [(hl, newFact)
                      , (hCurr, newFact)]
      _ -> mkFactBase []
-- Transfer our facts to target labels.
cloTransfer (FailT _ (F fl) (T tl)) f@(CloFact { currLabel = Just (curr, hCurr)
                                               , closureRefs
                                               , allClosures }) 
  = case Map.lookup curr closureRefs of
      Just cloInfo@(MkClo _ _) -> 
        let newFact = f { allClosures = Map.insert curr cloInfo allClosures } 
        in mkFactBase [(fl, newFact)
                      , (tl, newFact)
                      , (hCurr, newFact)]
      _ -> mkFactBase []

-- These instructions destroy any information
-- we have about a register - unknown if it is a function after
-- this.
cloTransfer (Open instr) f@(CloFact { closureRefs })
  | isJust dest = f { closureRefs = Map.insert (fromJust dest) Other closureRefs }
  | otherwise = f
    where
      dest = case instr of
               H.Enter _ _ d -> Just d
               H.AllocD d _ _ -> Just d
               H.Copy _ d -> Just d
               H.Store _ (d, _) -> Just d
               H.Set d _ -> Just d
               _ -> Nothing

-- These conditions don't matter when we don't have a current label.
cloTransfer (Ret _) _ = mkFactBase []
cloTransfer (Jmp _ _) _ = mkFactBase []
cloTransfer (FailT _ _ _) _ = mkFactBase []
cloTransfer (Halt _) _ = mkFactBase []
cloTransfer (Error _) _ = mkFactBase []


cloRewrite :: FwdRewrite InstrNode CloFact
cloRewrite = shallowFwdRw rewrite
  where
    rewrite :: SimpleFwdRewrite InstrNode CloFact
    rewrite i@(Open (H.MkClo _ _ _)) f =
      Just $ catGraphs [mkMiddle (Open (H.Note (show f)))
                       , mkMiddle i]
    rewrite i@(Ret _) f = Just $ mkMiddle (Open (H.Note (show f))) <*> mkLast i
    rewrite _ _ = Nothing
