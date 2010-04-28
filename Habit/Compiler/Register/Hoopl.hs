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
import Data.List (foldl')
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

-- | Converts a group to a graph. Maintains a dictionary which maps
-- machine labels to Hoopl labels. 
groupToBody :: C.Group -> FuelMonad (AGraph InstrNode C C)
groupToBody (groupLabel, groupCount, codes) = codesToBody' Map.empty codes >>= return . snd
  where
      -- The contortions here result from FailT's
      -- definition -- it only specifies the "false" branch. Hoopl needs a branch following
      -- all closed definitions. Have to ensure we have a Hoopl label for the "true" branch
      -- on FailT.      
      codesToBody' :: MLabelMap -> [C.Code] -> FuelMonad (MLabelMap, AGraph InstrNode C C)
      codesToBody' prevLbls ((entry, instrs):rest) 
          | null instrs = error "TODO: empty code block"
          | null rest = mkGraph 
          | otherwise = do 
              (lbls', graph) <- mkGraph 
              (lbls'', graph') <- codesToBody' lbls' rest
              return $ (lbls'', graph |*><*| graph')
        where
          (newLbls, entryLabel) = findLabel prevLbls entry entryL
          mkGraph = do
            (lbls'', last) <- end (last instrs)
            return $ (lbls'', mkFirst first <*> catGraphs (map middle (init instrs)) <*> mkLast last)
          first 
              | entry == groupLabel = EntryLabel (G entry) groupCount entryLabel
              | otherwise = LabelNode (G groupLabel) (N entry) entryLabel
          middle i = case i of 
                       H.Halt -> err "Illegal instruction in middle of block."
                       H.Ret _ -> err "Illegal instruction in middle of block."
                       H.Jmp _ -> err "Illegal instruction in middle of block."
                       H.Error _ -> err "Illegal instruction in middle of block."
                       _ -> mkMiddle $ Open i
          end :: H.Instr -> FuelMonad (MLabelMap, InstrNode O C)
          end i = do
            case i of
              H.Ret _ -> return (newLbls, Ret i)
              H.Jmp l -> do
                     fresh <- freshLabel
                     let (lbls', foundL) = findLabel newLbls l fresh
                     return (lbls', Closed i foundL)
              H.Halt -> return (newLbls, Halt i)
              H.FailT _ _ (H.F f) (H.S s)_ -> withFreshLabels $ \(t, f) -> do
                     let (lbls', falseL) = findLabel newLbls f fresh
                         (lbls'', trueL) = findLabel lbls' t fresh
                     return (lbls'', FailT i (F falseL) (T trueL))
              H.Error _ -> return (newLbls, Error i)
              _ -> err "Illegal instruction at end of code block."
          err msg = codeError (msg ++ " " ++ show instrs ++ " " ++ show rest)
          -- Find label associated with l, or associate label l
          -- with the fresh label given.
          findLabel :: MLabelMap -> C.Label -> Label -> (MLabelMap, Label)
          findLabel lbls l fresh = case Map.lookup l lbls of
                                     Just lbl -> (lbls, lbl)
                                     Nothing -> (Map.insert l fresh lbls, fresh)
      codesToBody' _ _ [] = error $ "Empty code block!"

-- | Retrieve the body of a graph.
bodyOf :: AGraph InstrNode C C -> FuelMonad (Body InstrNode)
bodyOf aGraph = do
  (GMany _ b _) <- graphOfAGraph aGraph
  return b

type GroupMap = Map C.Label C.Group
type BlockL = (Label, Block InstrNode C C)

-- | Recreate program instructions from Body. Still need to 
-- remove generated labels by sewing code back together.
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
    mkGroups (lbls, groups) (label, block) 
      | usedBlock lbls (label, block) = (lbls, groups)
      | otherwise = 
          let succBlocks = filter (not . usedBlock lbls) . allSucc $ (label, block)
              lbls' = foldl extendLabelSet lbls (label : map fst succBlocks)
          in (lbls', addToGroup groups (label, block) succBlocks)
    addToGroup :: GroupMap -> BlockL -> [BlockL] -> GroupMap
    addToGroup groups (l, entryB) rest =
      let (grp, cnt) :: (C.Label, Int) = case blockLabel entryB of
                                           EntryLabel (G l) cnt _ -> (l, cnt)
                                           LabelNode _ (N l) _ -> (l, 0)
      in Map.insert grp (grp, cnt, toCode (l, entryB) : map toCode rest) groups 
    usedBlock :: LabelSet -> BlockL -> Bool
    usedBlock lbls (label, _) = elemLabelSet label lbls 
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
    getBlock l = (l, fromMaybe (codeError $ "Block " ++ show l ++ " not found in bodyMap.") 
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

codeError :: String -> a
codeError msg = error msg
                          