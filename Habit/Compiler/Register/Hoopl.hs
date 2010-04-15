{-# LANGUAGE GADTs #-}
module Habit.Compiler.Register.Hoopl

where

import Compiler.Hoopl

import qualified Habit.Compiler.Register.Machine as M (Instr(..), Reg, Label)
import qualified Habit.Compiler.Register.Compiler as C

data InstrNode e x where
  LabelNode :: M.Instr -- ^ Original instruction
            -> Label -- ^ Numeric label
            -> InstrNode C O
  Enter :: M.Instr -- ^ Original instruction
        -> InstrNode O O
  Copy :: M.Instr -- ^ Original instruction
       -> InstrNode O O
  Ret :: M.Instr -- ^ Original instruction
         -> InstrNode O C
  Halt :: M.Instr -- ^ Original instruction
         -> InstrNode O C
  Rest :: M.Instr -- ^ Original instruction
       -> InstrNode O O

instance Edges InstrNode where
  entryLabel (LabelNode _ l) = l
  successors (Ret _) = []

-- | Turn a group into a body.  Probably need
-- to maintain map of Machine labels to Hoopl labels,
-- or use a hash function to turn Machine labels
-- into Hoopl lables.
makeBody :: C.Group -> FuelMonad (Label, Body InstrNode)
makeBody _ = do
  (l, g) <- prog 
  return $ (l, bodyOf g)
{-makeBody (_, _, blocks) = do
  -- Turn a list of blocks into a body.
  let toBody :: Block InstrNode O C -> Block InstrNode e x -> Body InstrNode
      toBody fst blks 
        | null blks = BodyEmpty
        | null (drop 1 blks) = BodyUnit (head blks)
        | otherwise = foldl1 BodyCat . map BodyUnit $ blks

      -- Turn a list of instructions into a block.
      toBlock :: (C.Label, [M.Instr]) -> FuelMonad (Block InstrNode C C)
      toBlock (lab, instrs) 
              | null instrs = return $ start `BCat` BUnit (Halt M.Halt)
              | otherwise = do
                  let body = foldl1 (BCat) . map (BUnit . mkNode) . init $ instrs
                      end = BUnit $ case last instrs of
                                       i@(M.Ret _) -> Ret i
                                       i@M.Halt -> Halt i
                                       i -> error $ "Block ended with " ++ show i ++ " unexpectedly. " ++ show instrs
                  return $ start `BCat` body `BCat` end
              where
                start = BUnit . LabelNode (M.Label lab) $ hash lab

      -- Turn a (string) label into a numeric label
      hash :: String -> Label
      hash = Label . sum . map ord

      -- Turn a machine instruction into a InstrNode
      mkNode instr@(M.Enter _ _ _) = Enter instr
      mkNode instr@(M.Copy _ _) = Copy instr
      mkNode instr = Rest instr
  mapM toBlock blocks >>= return . toBody-}

bodyOf :: Graph InstrNode C C -> Body InstrNode
bodyOf (GMany NothingO b NothingO) = b

prog :: FuelMonad (Label, Graph InstrNode C C)
prog = do
    topLabel <- freshLabel
    g <- top topLabel `unionBlocks` lab1
                     `unionBlocks` lab2
                     `unionBlocks` lab0
                     `unionBlocks` lab3
    return $ (topLabel, g)
  where
    top entry = 
      mkFirst (LabelNode (M.Label "TOP") entry) <*>
              catAGraphs [mkMiddle (Rest (M.AllocD "globComp_A4" "Comp.A" 0))
                         , mkMiddle (Rest (M.AllocC "globComp_id5" "lab1" 0))
                         , mkMiddle (Rest (M.AllocC "globComp_comp6" "lab0" 0))
                         , mkMiddle (Enter (M.Enter "globComp_comp6" "globComp_id5" "reg7"))
                         , mkMiddle (Enter (M.Enter "reg7" "globComp_id5" "reg8"))
                         , mkMiddle (Enter (M.Enter "reg8" "globComp_A4" "reg9"))
                         , mkMiddle (Copy (M.Copy "reg9" "globComp_main10"))] <*> 
          mkLast (Ret (M.Ret "globComp_main10"))
    lab1 = do
      l1 <- freshLabel
      mkFirst (LabelNode (M.Label "lab1") l1) <*>
              mkMiddle (Copy (M.Copy "arg" "reg11")) <*>
              mkLast (Ret (M.Ret "reg11"))
    lab0 = do
      l0 <- freshLabel
      mkFirst (LabelNode (M.Label "lab0") l0) <*>
              catAGraphs [ mkMiddle (Rest (M.AllocC "reg12" "lab2" 1))
                         , mkMiddle (Rest (M.Store "arg" ("reg12",0)))] <*>
              mkLast (Ret (M.Ret "reg12"))
    lab2 = do
      l2 <- freshLabel
      mkFirst (LabelNode (M.Label "lab2") l2) <*>
              catAGraphs [ mkMiddle (Rest (M.Load ("clo",0) "reg13"))
                         , mkMiddle (Rest (M.AllocC "reg14" "lab3" 2))
                         , mkMiddle (Rest (M.Store "reg13" ("reg14",0)))
                         , mkMiddle (Rest (M.Store "arg" ("reg14",1)))] <*>
              mkLast (Ret (M.Ret "reg14"))
    lab3 = do
      l3 <- freshLabel
      mkFirst (LabelNode (M.Label "lab3") l3) <*>
              catAGraphs [ mkMiddle (Rest (M.Load ("clo",0) "reg15"))
                         , mkMiddle (Rest (M.Load ("clo",1) "reg16"))
                         , mkMiddle (Enter (M.Enter "reg16" "arg" "reg17"))
                         , mkMiddle (Enter (M.Enter "reg15" "reg17" "reg18"))
                         , mkMiddle (Copy (M.Copy "reg18" "reg19"))] <*>
              mkLast (Ret (M.Ret "reg19"))


