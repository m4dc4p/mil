{-# LANGUAGE GADTs, NamedFieldPuns  #-}
{-# OPTIONS_GHC -Wall #-}
module Habit.Compiler.Register.ClosureElimination (cloOpt)

where

import Compiler.Hoopl
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

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
                              , fact_extend = undefined -- stdMapJoin extendFact
                              , fact_do_logging = True }
{-  where
    extendFact _ (OldFact old) (NewFact new) 
      | old == new = (NoChange, old)
      | otherwise = (SomeChange, new) -}
                                           

cloTransfer :: FwdTransfer InstrNode CloFact
cloTransfer (EntryLabel (G l) _ hl) f = 
  let fact = fromMaybe emptyFact $ lookupFact f hl
  in fact { currLabel = Just (l, hl) } 
cloTransfer (LabelNode _ (N l) hl) f = 
  let fact = fromMaybe emptyFact $ lookupFact f hl
  in fact { currLabel = Just (l, hl) }

cloTransfer (Ret (H.Ret r)) f@(CloFact { currLabel = Just (curr, hCurr)
                                       , closureRefs
                                       , allClosures }) 
  = case Map.lookup curr closureRefs of
      Just cloInfo@(MkClo _ _) -> mkFactBase [(hCurr, f { allClosures = Map.insert curr cloInfo allClosures })]
      _ -> mkFactBase []
cloTransfer (Ret _) _ = mkFactBase []

cloTransfer (Open (H.MkClo r curr regs)) f@(CloFact { closureRefs }) = 
  let cloInfo = MkClo curr (length regs)
  in f { closureRefs = Map.insert curr cloInfo closureRefs } 

cloTransfer (Open (H.Enter src arg dest)) f@(CloFact { closureRefs }) 
  = f { closureRefs = Map.insert dest Other closureRefs }
cloTransfer (Open (H.AllocD dest _ _)) f@(CloFact { closureRefs })  
  = f { closureRefs = Map.insert dest Other closureRefs }
cloTransfer (Open (H.Copy _ dest)) f@(CloFact { closureRefs }) 
  = f { closureRefs = Map.insert dest Other closureRefs }
cloTransfer (Open (H.Store src (dest, _))) f@(CloFact { closureRefs }) 
  = f { closureRefs = Map.insert dest Other closureRefs }
cloTransfer (Open (H.Set dest _)) f@(CloFact { closureRefs }) 
  = f { closureRefs = Map.insert dest Other closureRefs }
cloTransfer (Open _) f = f
cloTransfer (Jmp _ hl) f@(CloFact { currLabel = Just (curr, hCurr)
                                  , closureRefs
                                  , allClosures }) 
  = case Map.lookup curr closureRefs of
      Just cloInfo@(MkClo _ _) -> 
        let newFact = f { allClosures = Map.insert curr cloInfo allClosures } 
        in mkFactBase [(hl, newFact)
                      , (hCurr, newFact)]
      _ -> mkFactBase []
cloTransfer (Jmp _ hl) _ = mkFactBase []

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
cloTransfer (FailT _ _ _) _ = mkFactBase []

cloTransfer (Halt _) _ = mkFactBase []
cloTransfer (Error _) _ = mkFactBase []


cloRewrite :: FwdRewrite InstrNode CloFact
cloRewrite = undefined {-shallowFwdRw rewrite
  where
    rewrite :: SimpleFwdRewrite InstrNode CloFact
    rewrite i@(Open (H.MkClo _ l _)) fact =
      case fact of
        Return _ _ _ -> 
          let note = l ++ ": " ++ show fact 
          in Just $ catGraphs [mkMiddle (Open (H.Note note))
                                         , mkMiddle i]
        Other -> Nothing
    rewrite _ _ = Nothing-}

