{-# LANGUAGE GADTs, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall 	-fno-warn-name-shadowing #-}
module Habit.Compiler.Register.Hoopl 
  (groupsToBody, InstrNode(..) , bodyToGroups
  , Group(..), Norm(..), False(..), True(..) 
  , stdMapJoin)
   
where

import Compiler.Hoopl
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad (foldM)
import Data.List (foldl', nubBy)
import Data.Maybe (fromMaybe)

import qualified Habit.Compiler.Register.Machine as H
import qualified Habit.Compiler.Register.Compiler as C

-- | Maps machine IR to Hoopl's node types.
data InstrNode e x where
  -- | A label which starts a procedure (i.e., can be the
  -- target of an Enter instruction).
  EntryLabel 
    :: Group -- ^ Label which defined the group.
    -> Int -- ^ Number of arguments expected.
    -> Label -- ^ Hoopl label
    -> InstrNode C O
  -- | A Label that does not start a procedure.
  LabelNode 
    :: Group -- ^ Group this label belonged to.
    -> Norm -- ^ Label for this block.
    -> Label -- ^ Hoopl label mapped to original label.
    -> InstrNode C O
  -- | Generic open/open instruction.
  Open 
    :: H.Instr -- ^ Original instruction
    -> InstrNode O O
  -- | An instruction which can branch to the label given. 
  Closed 
    :: H.Instr -- ^ Original instruction
    -> Label -- ^ Next node
    -> InstrNode O C
  -- | QED
  FailT 
    :: H.Instr -- ^ Original instruction.
    -> False -- ^ Destination if test fails.
    -> True -- ^ Destination if test succeeds.
    -> InstrNode O C
  -- | QED.
  Ret 
    :: H.Instr -- ^ Original instruction
    -> InstrNode O C
  -- | QED.
  Halt 
    :: H.Instr -- ^ Original instruction
    -> InstrNode O C
  -- | QED.
  Error 
    :: H.Instr -- ^ Original instruction
    -> InstrNode O C

-- | Label which heads up a group.
newtype Group = G H.Label
  deriving (Eq, Show)

-- | Non-group label.
newtype Norm = N H.Label
  deriving (Eq, Show)

-- | Label when FailT succeeds.
newtype True = T Label
  deriving (Eq, Show)

-- | Label when FailT fails.
newtype False = F Label
  deriving (Eq, Show)

instance Edges InstrNode where
  entryLabel (LabelNode _ _ l) = l
  entryLabel (EntryLabel _ _ l) = l
  successors (Ret _) = []
  successors (Error _) = []
  successors (Halt _) = []
  -- Order of successors is key to reconstructing the code stream later. true always
  -- follows FailT instruction.
  successors (FailT _ (F false) (T true)) = [true, false]
  successors (Closed _ next) = [next]

-- | Turn a list of groups into a body.  The first entry is
-- the "top" group, where execution begins.
groupsToBody :: [C.Group] -> FuelMonad (Label, Body InstrNode)
groupsToBody groups 
    | null groups = error "TODO: empty groups."
    | otherwise = do
        body <- (foldM mkGraph emptyClosedGraph .
                 map toBasicBlocks $ groups) >>= bodyOf 
        return (entry body, body)
  where
    entry = fst . head . bodyList
    mkGraph :: AGraph InstrNode C C -> C.Group -> FuelMonad (AGraph InstrNode C C)
    mkGraph prevGraph group@(_, _, codes)
      | null codes = return prevGraph
      | otherwise = do
          graph <- groupToBody group
          return $ prevGraph |*><*| graph

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
toBasicBlocks (gl, c, codes) = (gl, c, basicBlocks codes)
  where basicBlocks = concatMap toBB 
        -- The code list is reconstructed by keeping the
        -- first label with the first code block and
        -- adding blank labels everywhere else.
        toBB :: C.Code -> [C.Code]
        toBB (l, []) = [(l, [])] -- error?
        toBB (l, instrs) = 
          let labels = l : zipWith (++) (repeat (gl ++ "-" ++ l ++ "-hoop")) (map show [(1::Int)..])
              -- Have to create new labels here which will not collide. Ugly ....
          in zip labels . uncurry (:) . foldr mkBB ([last instrs], []) $ (init instrs)
        mkBB :: H.Instr -> ([H.Instr],[[H.Instr]]) -> ([H.Instr],[[H.Instr]])
        mkBB instr (basic, list) = 
          -- Split blocks when we see "closed" instructions (conditional,
          -- jump, error, halt or return). Accumulate
          -- instructions for current block in "basic" until
          -- a closed instruction is seen, then move current "basic"
          -- to list and start accumlating a new basic. Remember
          -- we are going backwards through each block. 
          case instr of
            H.FailT _ _ _ _ -> ([instr], basic : list)
            H.Jmp _ -> ([instr], basic : list)
            H.Halt -> ([instr], basic : list)
            H.Ret _ -> ([instr], basic : list)
            H.Error _ -> ([instr], basic : list)
            _ -> (instr : basic, list)

type MLabelMap = Map H.Label Label

-- | Converts a group to a graph.  
groupToBody :: C.Group -> FuelMonad (AGraph InstrNode C C)
groupToBody (groupLabel, groupCount, codes) = codesToBody' Map.empty codes >>= return . snd
  where
      codesToBody' :: MLabelMap -> [C.Code] -> FuelMonad (MLabelMap, AGraph InstrNode C C)
      codesToBody' _ [] = error $ "Empty code block!"
      codesToBody' labels ((entry, instrs):rest) 
          | null instrs = error "TODO: empty code block"
          | null rest = mkGraph labels instrs entry 
          | otherwise = do 
              (lbls'', graph) <- mkGraph labels instrs entry 
              (lbls''', graph') <- codesToBody' lbls'' rest
              return $ (lbls''', graph |*><*| graph')
      mkGraph labels instrs entry = do
          (labels', start) <- first labels entry 
          (labels'', last) <- end labels' (last instrs)
          return $ (labels''
                   , mkFirst start
                    <*> catGraphs (map middle (init instrs)) 
                    <*> mkLast last)
      first labels entry = do
          (labels', label) <- newLabel labels entry
          return (labels'
                 , if entry == groupLabel 
                   then EntryLabel (G entry) groupCount label
                   else LabelNode (G groupLabel) (N entry) label)
      middle i = case i of 
                   H.Halt -> error $ "Illegal instruction in middle of block: " ++ show i
                   H.Ret _ -> error $ "Illegal instruction in middle of block: " ++ show i
                   H.Jmp _ -> error $ "Illegal instruction in middle of block: " ++ show i
                   H.Error _ -> error $ "Illegal instruction in middle of block: " ++ show i
                   H.FailT { } -> error $ "Illegal instruction in middle of block: " ++ show i
                   _ -> mkMiddle $ Open i
      end :: MLabelMap -> H.Instr -> FuelMonad (MLabelMap, InstrNode O C)
      end labels i = do
          case i of
            H.Ret _ -> return (labels, Ret i)
            H.Jmp l -> do
                       (labels', foundL) <- newLabel labels l 
                       return (labels', Closed i foundL)
            H.Halt -> return (labels, Halt i)
            H.FailT _ _ (H.F f) (H.S t) -> do
                       (labels', falseL) <- newLabel labels f
                       (labels'', trueL) <- newLabel labels' t
                       return (labels'', FailT i (F falseL) (T trueL))
            H.Error _ -> return (labels, Error i)
            _ -> error $ "Illegal instruction at end of code block: " ++ show i
      -- Find label associated with l, or associate label l
      -- with the fresh label given.
      newLabel :: MLabelMap -> H.Label -> FuelMonad (MLabelMap, Label)
      newLabel lbls e = 
        case Map.lookup e lbls of
          Just lbl -> return (lbls, lbl)
          Nothing -> do
            fresh <- freshLabel
            return (Map.insert e fresh lbls, fresh)

-- | Retrieve the body of a graph.
bodyOf :: AGraph InstrNode C C -> FuelMonad (Body InstrNode)
bodyOf aGraph = do
  (GMany _ b _) <- graphOfAGraph aGraph
  return b

type GroupMap = Map C.Label C.Group
type BlockL = (Label, Block InstrNode C C)

-- | Recreate program instructions from Body. 
bodyToGroups :: Body InstrNode -> [C.Group]
bodyToGroups body = Map.elems . snd . 
                    foldl' mkGroups (emptyLabelSet, Map.empty) .
                    filter entryNode . bodyList $ body
  where
    bodyM = bodyMap body
    entryNode :: BlockL -> Bool
    entryNode (_, block) = case blockLabel block of
                             LabelNode _ _ _ -> False
                             EntryLabel _ _ _ -> True
    mkGroups :: (LabelSet, GroupMap) -> BlockL -> (LabelSet, GroupMap)
    mkGroups (lbls, groups) blockL
      | usedBlock lbls blockL = (lbls, groups)
      | otherwise = 
          let succBlocks = newSuccessors lbls blockL
              lbls' = foldl extendLabelSet lbls (fst blockL : map fst succBlocks)
          in (lbls', addToGroup groups blockL succBlocks)
    addToGroup :: GroupMap -> BlockL -> [BlockL] -> GroupMap
    addToGroup groups (l, entryB) rest =
      let (grp, cnt) :: (C.Label, Int) = case blockLabel entryB of
                                           EntryLabel (G l) cnt _ -> (l, cnt)
                                           LabelNode _ (N l) _ -> (l, 0)
      in Map.insert grp (grp, cnt, toCode (l, entryB) : map toCode rest) groups 
    -- | Return all unique, unused successors to the given block. The filter
    -- ensures only blocks that are new are returned. A new, duplicate block
    -- can appear, though, so we use nubBy to get distinct blocks.
    newSuccessors :: LabelSet -> BlockL -> [BlockL]
    newSuccessors lbls = nubBy blockEq . filter (not . usedBlock lbls) . allSucc 
    usedBlock :: LabelSet -> BlockL -> Bool
    usedBlock lbls (label, _) = elemLabelSet label lbls 
    blockEq :: BlockL -> BlockL -> Bool
    blockEq (l1, _) (l2, _) = l1 == l2
    -- Return all the successors of the given block, including all 
    -- of their successors, and so on, in the order in which they appear
    -- when successors is called.
    allSucc :: BlockL -> [BlockL]
    allSucc blockL = 
      case getSuccessors blockL of
        [] -> []
        ss -> concatMap (\bl -> bl : allSucc bl) ss
    getSuccessors :: BlockL -> [BlockL]
    getSuccessors (_, block) = map getBlock (successors block)
    -- All blocks should be found here, so we don't return Maybe type.
    getBlock :: Label -> (Label, Block InstrNode C C)
    getBlock l = (l, fromMaybe (error $ "Block " ++ show l ++ " not found in bodyMap.") 
                           (lookupLabel bodyM l))
    -- | Convert a hoopl basic block to a machine basic block.
    toCode :: BlockL -> C.Code
    toCode (_, block) = (label, code block)
      where
        label :: C.Label
        label = case blockLabel block of
                  LabelNode _ (N l) _ -> l 
                  EntryLabel (G l) _ _ -> l
        code :: Block InstrNode e x -> [H.Instr]
        code (b1 `BCat` b2) = code b1 ++ code b2
        code (BUnit instr) = 
          case instr of
            LabelNode _ _ _ -> []
            EntryLabel _ _ _ -> []
            Closed i _ -> [i]
            Ret i -> [i]
            FailT i _ _ -> [i]
            Halt i -> [i] 
            Error i -> [i] 
            Open i -> [i]

-- | Retrieve the label associated with this block.    
blockLabel :: Block InstrNode e x -> InstrNode C O
blockLabel (b1 `BCat` _) = blockLabel b1
blockLabel (BUnit i@(LabelNode _ _ _)) = i    
blockLabel (BUnit i@(EntryLabel _ _ _)) = i    
blockLabel _ = error $ "Block did not start with label."

-- | It's common to represent dataflow facts as a map from locations
-- to some fact about the locations. For these maps, the join
-- operation on the map can be expressed in terms of the join
-- on each element:
-- Stolen shamelessly from Hoopl source ...
stdMapJoin :: Ord k => JoinFun v -> JoinFun (Map k v)
stdMapJoin eltJoin l (OldFact old) (NewFact new) = Map.foldWithKey add (NoChange, old) new
  where 
    add k new_v (ch, joinmap) =
      case Map.lookup k joinmap of
        Nothing    -> (SomeChange, Map.insert k new_v joinmap)
        Just old_v -> case eltJoin l (OldFact old_v) (NewFact new_v) of
                        (SomeChange, v') -> (SomeChange, Map.insert k v' joinmap)
                        (NoChange,   _)  -> (ch, joinmap)
