{-# LANGUAGE GADTs, ScopedTypeVariables #-}
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
  -- | A label which starts a procedure (i.e., can be the
  -- target of an Enter instruction.
  EntryLabel :: M.Label -- ^ Label which defined the group.
                -> Int -- ^ Number of arguments expected.
                -> Label -- ^ Hoopl label
                -> InstrNode C O
  LabelNode :: M.Label -- ^ Group this label belonged to.
            -> M.Label -- ^ Label for this block.
            -> Label -- ^ Hoopl label mapped to original label.
            -> InstrNode C O
  Open :: M.Instr -- ^ Original instruction
       -> InstrNode O O
  FailT :: M.Instr -- ^ Original instruction.
        -> Label -- ^ Destination if test fails.
        -> Label -- ^ Destination if test succeeds.
        -> InstrNode O C
  -- | An instruction which can branch to the label given. 
  Closed1 :: M.Instr -- ^ Original instruction
        -> Label -- ^ Next node
        -> InstrNode O C
  Ret :: M.Instr -- ^ Original instruction
      -> InstrNode O C
  Halt :: M.Instr -- ^ Original instruction
       -> InstrNode O C
  Error :: M.Instr -- ^ Original instruction
        -> InstrNode O C

instance Edges InstrNode where
  entryLabel (LabelNode _ _ l) = l
  entryLabel (EntryLabel _ _ l) = l
  successors (Ret _) = []
  successors (Error _) = []
  successors (Halt _) = []
  successors (FailT _ true false) = [true, false]
  successors (Closed1 _ next) = [next]

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

-- | Convert codes in a group to basic blocks, so 
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
  where basicBlocks = concatMap toBB $ codes
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
                                              
groupToBody :: C.Group -> AGraph InstrNode C C
groupToBody (l, c, codes) 
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
      codesToBody l c (mkMap codes) ls codes

type MLabelMap = Map M.Label Label

codesToBody :: C.Label -> Int -> MLabelMap -> [Label] -> [C.Code] -> AGraph InstrNode C C
codesToBody groupLabel groupCount lbls (curr:ls) ((entry, instrs):rest) 
    | null instrs = error "TODO: empty code block"
    | null rest = graph
    | otherwise = graph <#> codesToBody groupLabel groupCount lbls ls rest
  where
    nextLabel = head ls
    mkLabel l 
      | l == groupLabel = EntryLabel l groupCount curr
      | otherwise = LabelNode groupLabel l curr
    graph = mkFirst (mkLabel entry) <*>
            catAGraphs (map middle (init instrs)) <*>
            mkLast (end (last instrs))
    middle i = case i of 
                 M.Halt -> codeError "Illegal instruction in middle of block."
                 M.Ret _ -> codeError "Illegal instruction in middle of block."
                 M.Jmp _ -> codeError "Illegal instruction in middle of block."
                 M.Error _ -> codeError "Illegal instruction in middle of block."
                 _ -> mkMiddle $ Open i
    end i = case i of
              M.Enter _ _ _ -> Closed1 i nextLabel
              M.Ret _ -> Ret i
              M.Jmp l -> Closed1 i (findLabel l)
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

bodyToGroups :: Body InstrNode -> [C.Group]
bodyToGroups = map clean . Map.elems . foldr toGroups Map.empty . map snd . bodyList 
  where
    clean :: C.Group -> C.Group 
    clean (l, c, cs) = 
      let (first, rest) = (head cs, tail cs)
      in (l, c, foldl removeEmptyLabels [first] $ rest)
    toGroups :: Block InstrNode C C -> Map C.Label C.Group -> Map C.Label C.Group 
    toGroups block groups = 
      let (groupLabel, info) :: (M.Label, Either M.Label Int) = 
            case blockLabel block of
              LabelNode group lab _ -> (group, Left lab)
              EntryLabel group cnt _ -> (group, Right cnt)
      in case Map.lookup groupLabel groups of
           Just (l, c, cs) -> 
             case info of
               Left lab -> Map.insert groupLabel (l, c, cs ++ [(lab, toCode block)]) groups
               Right cnt -> Map.insert groupLabel (l, cnt, (groupLabel, toCode block) : cs) groups
           Nothing -> 
             case info of
               Left lab -> Map.insert groupLabel (groupLabel, 0, [(lab, toCode block)]) groups
               Right cnt -> Map.insert groupLabel (groupLabel, cnt, [(groupLabel, toCode block)]) groups
    blockLabel :: Block InstrNode e x -> InstrNode C O
    blockLabel (b1 `BCat` b2) = blockLabel b1
    blockLabel (BUnit i@(LabelNode _ _ _)) = i    
    blockLabel (BUnit i@(EntryLabel _ _ _)) = i    
    blockLabel _ = error $ "Block did not start with label."
    toCode :: Block InstrNode e x -> [M.Instr]
    toCode (b1 `BCat` b2) = toCode b1 ++ toCode b2
    toCode (BUnit i) = 
      case i of
        LabelNode _ l _ -> []
        EntryLabel l _ _ -> []
        Closed1 i _ -> [i]
        Ret i -> [i]
        FailT i _ _ -> [i]
        Halt i -> [i] 
        Error i -> [i] 
        Open i -> [i]
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
      mkFirst (EntryLabel "TOP" 0 entry) <*>
              catAGraphs [mkMiddle (Open (M.AllocD "globComp_A4" "Comp.A" 0))
                         , mkMiddle (Open (M.AllocC "globComp_id5" "lab1" 0))
                         , mkMiddle (Open (M.AllocC "globComp_comp6" "lab0" 0))] <*>
              mkLast (Closed1 (M.Enter "globComp_comp6" "globComp_id5" "reg7") l1) <#>
      mkFirst (LabelNode "TOP" "" l1) <*>
              mkLast (Closed1 (M.Enter "reg7" "globComp_id5" "reg8") l2) <#>
      mkFirst (LabelNode "TOP" "" l2) <*>
              mkLast (Closed1 (M.Enter "reg8" "globComp_A4" "reg9") l3) <#>
      mkFirst (LabelNode "TOP" "" l3) <*>
              mkMiddle (Open (M.Copy "reg9" "globComp_main10")) <*> 
              mkLast (Ret (M.Ret "globComp_main10"))
    lab1 = do
      l1 <- freshLabel
      mkFirst (EntryLabel "lab1" 0 l1) <*>
              mkMiddle (Open (M.Copy "arg" "reg11")) <*>
              mkLast (Ret (M.Ret "reg11"))
    lab0 = do
      l0 <- freshLabel
      mkFirst (EntryLabel "lab0" 0 l0) <*>
              catAGraphs [ mkMiddle (Open (M.AllocC "reg12" "lab2" 1))
                         , mkMiddle (Open (M.Store "arg" ("reg12",0)))] <*>
              mkLast (Ret (M.Ret "reg12"))
    lab2 = do
      l2 <- freshLabel
      mkFirst (EntryLabel "lab2" 1 l2) <*>
              catAGraphs [ mkMiddle (Open (M.Load ("clo",0) "reg13"))
                         , mkMiddle (Open (M.AllocC "reg14" "lab3" 2))
                         , mkMiddle (Open (M.Store "reg13" ("reg14",0)))
                         , mkMiddle (Open (M.Store "arg" ("reg14",1)))] <*>
              mkLast (Ret (M.Ret "reg14"))
    lab3 = withFreshLabels $ \(l1, l2, l3) -> 
      mkFirst (EntryLabel "lab3" 2 l1) <*>
              catAGraphs [ mkMiddle (Open (M.Load ("clo",0) "reg15"))
                         , mkMiddle (Open (M.Load ("clo",1) "reg16"))] <*>
              mkLast (Closed1 (M.Enter "reg16" "arg" "reg17") l2) <#>
      mkFirst (LabelNode "lab3" "" l2) <*>
              mkLast (Closed1 (M.Enter "reg15" "reg17" "reg18") l3) <#>
      mkFirst (LabelNode "lab3" "" l3) <*>
              mkMiddle (Open (M.Copy "reg18" "reg19")) <*>
              mkLast (Ret (M.Ret "reg19")) 


