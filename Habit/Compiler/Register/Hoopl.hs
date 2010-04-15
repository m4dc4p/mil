{-# LANGUAGE GADTs #-}
module Habit.Compiler.Register.Hoopl 
  (groupsToBody, InstrNode(..) , bodyToGroups)
   
where

import Compiler.Hoopl
import Data.Map (Map)

import qualified Habit.Compiler.Register.Machine as M (Instr(..), Reg, Label)
import qualified Habit.Compiler.Register.Compiler as C

-- | Maps machine IR to Hoopl's node types.
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
  FailT :: M.Instr -- ^ Original instruction.
        -> InstrNode O C
  Halt :: M.Instr -- ^ Original instruction
         -> InstrNode O C
  Jmp :: M.Instr -- ^ Original instruction
         -> InstrNode O C
  Error :: M.Instr -- ^ Original instruction
         -> InstrNode O C
  Rest :: M.Instr -- ^ Original instruction
       -> InstrNode O O

instance Edges InstrNode where
  entryLabel (LabelNode _ l) = l
  successors (Ret _) = []

type LabelMap = Map Label M.Label

-- | Turn a list of groups into a body.  The first entry is
-- the "top" group, where execution begins.
-- to maintain map of Machine labels to Hoopl labels,
-- or use a hash function to turn Machine labels
-- into Hoopl lables.
groupsToBody :: [C.Group] -> FuelMonad (Label, Body InstrNode)
groupsToBody groups 
    | null groups = error "TODO: empty groups."
    | otherwise = do
        body <- foldl1 unionBlocks . map groupToBody $ groups
        return $ (fst . head . bodyList $ bodyOf body, bodyOf body)

groupToBody :: C.Group -> AGraph InstrNode C C
groupToBody (_, _, codes) 
  | null codes = error "TODO: empty code blocks"
  | otherwise = let notNote (M.Note _) = False
                    notNote _ = True
                in codesToBody . map (\(l, instrs) -> (l, filter notNote instrs)) $ codes

-- | TODO: Convert codes in a group to basic blocks, so 
-- all transfers show up correctly. Will need to rewrite
-- labels.
toBasicBlocks :: C.Group -> C.Group
toBasicBlocks = undefined

codesToBody :: [C.Code] -> AGraph InstrNode C C
codesToBody ((entry, instrs):rest) 
    | null instrs = error "TODO: empty code block"
    | otherwise = do
        l <- freshLabel
        let g = mkFirst (LabelNode (M.Label entry) l) <*>
                  catAGraphs (map middle instrs) <*>
                  mkLast (end (last instrs))
        if null rest
         then g
         else g `unionBlocks` codesToBody rest
  where
    middle i = case i of 
                 (M.Enter _ _ _) -> mkMiddle $ Enter i
                 (M.Copy _ _) -> mkMiddle $ Copy i
                 M.Halt -> emptyAGraph
                 (M.Ret _) -> emptyAGraph
                 (M.Jmp _) -> emptyAGraph
                 (M.Error _) -> emptyAGraph
                 _ -> mkMiddle $ Rest i
    end i = case i of
              (M.Ret _) -> Ret i
              M.Halt -> Halt i
              (M.FailT _ _ _) -> FailT i
              (M.Jmp _) -> Jmp i
              (M.Error _) -> Error i
              _ -> codeError "Illegal instruction at end of code block."
    codeError msg = error (msg ++ " " ++ show instrs ++ " " ++ show rest)

-- | Turn a body back into a Group of Machine instructions. 
bodyToGroups :: Body InstrNode -> [C.Group]
bodyToGroups = map toGroup . reverse . bodyList
  where
    toGroup :: (Label, Block InstrNode e x) -> C.Group
    toGroup (_, block) = 
      let ((M.Label l):instrs) = toCode block
      in (l, 0, [(l, instrs)]) -- Ugly: assume first instruction always a label.
    toCode :: Block InstrNode e x -> [M.Instr]
    toCode (BUnit i) = [toInstr i]
    toCode (b1 `BCat` b2) = toCode b1 ++ toCode b2
    toInstr :: InstrNode e x -> M.Instr
    toInstr (LabelNode i l) = i
    toInstr (Enter i) = i
    toInstr (Copy i) = i
    toInstr (Ret i) = i
    toInstr (FailT i) = i
    toInstr (Halt i) = i 
    toInstr (Jmp i) = i 
    toInstr (Error i) = i 
    toInstr (Rest i) = i

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


