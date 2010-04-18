{-# LANGUAGE GADTs #-}
module Habit.Compiler.Register.Hoopl 
  (groupsToBody, InstrNode(..) , bodyToGroups)
   
where

import Compiler.Hoopl
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Habit.Compiler.Register.Machine as M (Instr(..), Reg, Label)
import qualified Habit.Compiler.Register.Compiler as C

-- | Maps machine IR to Hoopl's node types.
data InstrNode e x where
  LabelNode :: M.Instr -- ^ Original instruction
            -> Label -- ^ Numeric label
            -> InstrNode C O
  Rest :: M.Instr -- ^ Original instruction
       -> InstrNode O O
  Enter :: M.Instr -- ^ Original instruction
        -> Label -- ^ Next node
        -> InstrNode O C
  FailT :: M.Instr -- ^ Original instruction.
        -> Label -- ^ Destination if test fails.
        -> Label -- ^ Destination if test succeeds.
        -> InstrNode O C
  Ret :: M.Instr -- ^ Original instruction
      -> InstrNode O C
  Jmp :: M.Instr -- ^ Original instruction
      -> Label -- ^ Destination.
      -> InstrNode O C
  Halt :: M.Instr -- ^ Original instruction
       -> InstrNode O C
  Error :: M.Instr -- ^ Original instruction
        -> InstrNode O C

instance Edges InstrNode where
  entryLabel (LabelNode _ l) = l
  successors (Ret _) = []
  successors (Error _) = []
  successors (Halt _) = []
  successors (Jmp _ dest) = [dest]
  successors (FailT _ true false) = [true, false]
  successors (Enter _ next) = [next]

-- | Turn a list of groups into a body.  The first entry is
-- the "top" group, where execution begins.
-- to maintain map of Machine labels to Hoopl labels,
-- or use a hash function to turn Machine labels
-- into Hoopl lables.
groupsToBody :: [C.Group] -> FuelMonad (Label, Body InstrNode)
groupsToBody groups 
    | null groups = error "TODO: empty groups."
    | otherwise = do
        body <- foldl1 unionBlocks . 
                map groupToBody .
                map toBasicBlocks $ groups
        return $ (fst . head . bodyList $ bodyOf body, bodyOf body)

-- | TODO: Convert codes in a group to basic blocks, so 
-- all transfers show up correctly. An empty
-- label implies the code block is the fall-through of
-- it's immediate predecessor.
--
-- This is a place where I slightly want to alter the 
-- AST so I can add custom labels (Nothing), but 
-- I don't want to rewrite all my code, or copy
-- the data structure. For now I use the ugly hack
-- of having empty labels
toBasicBlocks :: C.Group -> C.Group
toBasicBlocks (l, c, codes) = (l, c, basicBlocks)
  where basicBlocks = concatMap addJmps . concatMap toBB $ codes
        -- The code list is reconstructed by keeping the
        -- first label with the first code block and
        -- adding blank labels everywhere else.
        toBB :: C.Code -> [C.Code]
        toBB (l, []) = [(l, [])] -- error?
        toBB (l, instrs) = zip (l : repeat "") . 
                           uncurry (:) . 
                           foldr mkBB ([last instrs], []) $ (init instrs)
        mkBB :: M.Instr -> ([M.Instr],[[M.Instr]]) -> ([M.Instr],[[M.Instr]])
        mkBB instr (basic, list) = 
          -- Split blocks when we see "closed" instructions (conditional,
          -- jump, error, halt or return). Accumulate
          -- instructions for current block in "basic" until
          -- a closed instruction is seen, then move current "basic"
          -- to list and start accumlating a new basic. Remember
          -- we are going backwards through each block. 
          case instr of
            M.FailT _ _ _ -> ([instr], basic : list)
            M.Jmp _ -> ([instr], basic : list)
            M.Halt -> ([instr], basic : list)
            M.Enter _ _ _ -> ([instr], basic : list)
            M.Ret _ -> ([instr], basic : list)
            M.Error _ -> ([instr], basic : list)
            _ -> (instr : basic, list)
        -- Add jumps where labels are found in the middle
        -- of blocks. 
        addJmps :: C.Code -> [C.Code]
        addJmps (l, instrs) = append $ foldl go ([], (l, [])) instrs
          where
            append (cs, c) = cs ++ [c]
            -- Check if last instruction is already a jump, halt, return or
            -- error. If not, add jump to this label and split the block.
            -- Otherwise, just split the block.
            go :: ([C.Code], C.Code) -> M.Instr -> ([C.Code], C.Code) 
            go (accum, (_, [])) (M.Label l) = (accum, (l, []))
            go (accum, (l, instrs)) (M.Label newLabel) = 
              case last instrs of
                     M.Enter _ _ _ -> (accum ++ [(l, instrs)], (newLabel, []))
                     M.Ret _ -> (accum ++ [(l, instrs)], (newLabel, []))
                     M.FailT _ _ _ -> (accum ++ [(l, instrs)], (newLabel, []))
                     M.Halt -> (accum ++ [(l, instrs)], (newLabel, []))
                     M.Jmp _ -> (accum ++ [(l, instrs)], (newLabel, []))
                     M.Error _ -> (accum ++ [(l, instrs)], (newLabel, []))
                     _ -> (accum ++ [(l, append (instrs, M.Jmp newLabel))], (newLabel, []))
            go (accum, (l, instrs)) instr = (accum, (l, instrs ++ [instr]))
                                              
groupToBody :: C.Group -> AGraph InstrNode C C
groupToBody (_, _, codes) 
  | null codes = error "TODO: empty code blocks"
  | otherwise = do
      ls <- sequence . take (length codes) . repeat $ freshLabel
      -- This is pretty ugly. Map all named labels to a hoopl
      -- label so they are available when we translate to a body.
      --
      -- Empty labels are ignored because they were added to support fall-through
      -- when code was converted to basic blocks.
      --
      -- If only my IR was easier to modify and I could have true "anonymous"
      -- labels rather than these empty labels.
      let mkMap = foldl addLabel Map.empty . zip ls . map fst 
          addLabel lblMap (hLbl, []) = lblMap
          addLabel lblMap (hLbl, mLbl) = Map.insert mLbl hLbl lblMap
      codesToBody (mkMap codes) ls codes

type MLabelMap = Map M.Label Label

codesToBody :: MLabelMap -> [Label] -> [C.Code] -> AGraph InstrNode C C
codesToBody lbls (curr:ls) ((entry, instrs):rest) 
    | null instrs = error "TODO: empty code block"
    | null rest = graph
    | otherwise = graph <#> codesToBody lbls ls rest
  where
    nextLabel = head ls
    graph = mkFirst (LabelNode (M.Label entry) curr) <*>
            catAGraphs (map middle (init instrs)) <*>
            mkLast (end (last instrs))
    middle i = case i of 
                 M.Halt -> codeError "Illegal instruction in middle of block."
                 M.Ret _ -> codeError "Illegal instruction in middle of block."
                 M.Jmp _ -> codeError "Illegal instruction in middle of block."
                 M.Error _ -> codeError "Illegal instruction in middle of block."
                 _ -> mkMiddle $ Rest i
    end i = case i of
              M.Enter _ _ _ -> Enter i nextLabel
              M.Ret _ -> Ret i
              M.Jmp l -> Jmp i (findLabel l)
              M.Halt -> Halt i
              M.FailT _ _ l -> FailT i (findLabel l) nextLabel
              M.Error _ -> Error i
              _ -> codeError "Illegal instruction at end of code block."
    codeError msg = error (msg ++ " " ++ show instrs ++ " " ++ show rest)
    findLabel l = case Map.lookup l lbls of
                    Just lbl -> lbl
                    Nothing -> error $ "Failed to find " ++ 
                               show l ++ " when constructing body for " ++
                               show (entry, instrs) ++ show rest

-- | Turn a body back into a Group of Machine instructions. 
bodyToGroups :: Body InstrNode -> [C.Group]
bodyToGroups = foldl1 combine . map toGroup . reverse . bodyList
  where
    -- Lots of empty groups get created - fold them back
    -- into "real" groups. toGroup creates a list of singleton
    -- lists so we can use foldl1.
    combine :: [C.Group] -> [C.Group] -> [C.Group]
    combine groups [("", c, curr)] =
      let (pl, pn, prev) = last groups
          codes = foldl removeEmptyLabels prev curr
      -- drop initial label from each empty group.
      in init groups ++ [(pl, pn, codes)]
    combine groups group = groups ++ group
    toGroup :: (Label, Block InstrNode e x) -> [C.Group]
    toGroup (_, block) = 
      let ((M.Label l):instrs) = toCode block
      in [(l, 0, [(l, instrs)])] -- Ugly: assume first instruction always a label.
    toCode :: Block InstrNode e x -> [M.Instr]
    toCode (BUnit i) = [toInstr i]
    toCode (b1 `BCat` b2) = toCode b1 ++ toCode b2
    toInstr :: InstrNode e x -> M.Instr
    toInstr (LabelNode i l) = i
    toInstr (Enter i _) = i
    toInstr (Ret i) = i
    toInstr (FailT i _ _) = i
    toInstr (Halt i) = i 
    toInstr (Jmp i _) = i 
    toInstr (Error i) = i 
    toInstr (Rest i) = i

removeEmptyLabels :: [C.Code] -> C.Code -> [C.Code]
removeEmptyLabels codes ("", code) = 
      let sew :: C.Code -> [M.Instr] -> C.Code
          sew (l, is1) is2 = (l, is1 ++ is2)
      in case codes of 
           [] -> error $ "Blank label at head of group."
           [code'] -> [sew code' code]
           _ -> init codes ++ [sew (last codes) code]
removeEmptyLabels codes code = codes ++ [code]

bodyOf :: Graph InstrNode C C -> Body InstrNode
bodyOf (GMany NothingO b NothingO) = b

infixl 2 <#>
(<#>) = unionBlocks

prog :: FuelMonad (Label, Graph InstrNode C C)
prog = do
    topLabel <- freshLabel
    g <- top topLabel <#> 
         lab1 <#> 
         lab2 <#> 
         lab0 <#> 
         lab3
    return $ (topLabel, g)
  where
    top entry = withFreshLabels $ \(l1, l2, l3) -> 
      mkFirst (LabelNode (M.Label "TOP") entry) <*>
              catAGraphs [mkMiddle (Rest (M.AllocD "globComp_A4" "Comp.A" 0))
                         , mkMiddle (Rest (M.AllocC "globComp_id5" "lab1" 0))
                         , mkMiddle (Rest (M.AllocC "globComp_comp6" "lab0" 0))] <*>
              mkLast (Enter (M.Enter "globComp_comp6" "globComp_id5" "reg7") l1) <#>
      mkFirst (LabelNode (M.Label "") l1) <*>
              mkLast (Enter (M.Enter "reg7" "globComp_id5" "reg8") l2) <#>
      mkFirst (LabelNode (M.Label "") l2) <*>
              mkLast (Enter (M.Enter "reg8" "globComp_A4" "reg9") l3) <#>
      mkFirst (LabelNode (M.Label "") l3) <*>
              mkMiddle (Rest (M.Copy "reg9" "globComp_main10")) <*> 
              mkLast (Ret (M.Ret "globComp_main10"))
    lab1 = do
      l1 <- freshLabel
      mkFirst (LabelNode (M.Label "lab1") l1) <*>
              mkMiddle (Rest (M.Copy "arg" "reg11")) <*>
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
    lab3 = withFreshLabels $ \(l1, l2, l3) -> 
      mkFirst (LabelNode (M.Label "lab3") l1) <*>
              catAGraphs [ mkMiddle (Rest (M.Load ("clo",0) "reg15"))
                         , mkMiddle (Rest (M.Load ("clo",1) "reg16"))] <*>
              mkLast (Enter (M.Enter "reg16" "arg" "reg17") l2) <#>
      mkFirst (LabelNode (M.Label "lab3") l2) <*>
              mkLast (Enter (M.Enter "reg15" "reg17" "reg18") l3) <#>
      mkFirst (LabelNode (M.Label "lab3") l3) <*>
              mkMiddle (Rest (M.Copy "reg18" "reg19")) <*>
              mkLast (Ret (M.Ret "reg19")) 


