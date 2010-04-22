{-# LANGUAGE GADTs, ScopedTypeVariables #-}
module Habit.Compiler.Register.Hoopl 
  (groupsToBody, InstrNode(..) , bodyToGroups
  , stdMapJoin)
   
where

import Compiler.Hoopl
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad (foldM)

import qualified Habit.Compiler.Register.Machine as M (Instr(..), Label)
import qualified Habit.Compiler.Register.Compiler as C

infixl 2 <#>
-- | Convenience operator for glueing union-ing two blocks.
(<#>) :: AGraph n C C -> AGraph n C C -> AGraph n C C
(<#>) = unionBlocks

-- | Maps machine IR to Hoopl's node types.
data InstrNode e x where
  -- | A label which starts a procedure (i.e., can be the
  -- target of an Enter instruction).
  EntryLabel 
    :: M.Label -- ^ Label which defined the group.
    -> Int -- ^ Number of arguments expected.
    -> Label -- ^ Hoopl label
    -> InstrNode C O
  -- | A Label that does not start a procedure.
  LabelNode 
    :: M.Label -- ^ Group this label belonged to.
    -> M.Label -- ^ Label for this block.
    -> Label -- ^ Hoopl label mapped to original label.
    -> InstrNode C O
  -- | Generic open/open instruction.
  Open 
    :: M.Instr -- ^ Original instruction
    -> InstrNode O O
  -- | An instruction which can branch to the label given. 
  Closed 
    :: M.Instr -- ^ Original instruction
    -> Label -- ^ Next node
    -> InstrNode O C
  -- | QED
  FailT 
    :: M.Instr -- ^ Original instruction.
    -> Label -- ^ Destination if test fails.
    -> Label -- ^ Destination if test succeeds.
    -> InstrNode O C
  -- | QED.
  Ret 
    :: M.Instr -- ^ Original instruction
    -> InstrNode O C
  -- | QED.
  Halt 
    :: M.Instr -- ^ Original instruction
    -> InstrNode O C
  -- | QED.
  Error 
    :: M.Instr -- ^ Original instruction
    -> InstrNode O C

instance Edges InstrNode where
  entryLabel (LabelNode _ _ l) = l
  entryLabel (EntryLabel _ _ l) = l
  successors (Ret _) = []
  successors (Error _) = []
  successors (Halt _) = []
  successors (FailT _ true false) = [true, false]
  successors (Closed _ next) = [next]

-- | Turn a list of groups into a body.  The first entry is
-- the "top" group, where execution begins.
groupsToBody :: [C.Group] -> FuelMonad (Label, Body InstrNode)
groupsToBody groups 
    | null groups = error "TODO: empty groups."
    | otherwise = do
        body <- (foldM groupToBody (Map.empty, emptyClosedAGraph) .
                 map toBasicBlocks $ groups) >>= bodyOf . snd
        return (entry body, body)
  where
    entry = fst . head . bodyList
    groupToBody :: (MLabelMap, AGraph InstrNode C C) -> C.Group -> FuelMonad (MLabelMap, AGraph InstrNode C C) 
    groupToBody (lbls, prevGraph) group@(_, _, codes)
      | null codes = return (lbls, prevGraph)
      | otherwise = do
          (lbls', graph) <- codesToBody group lbls 
          return (lbls', prevGraph <#> graph)

-- | Converts a body back to a list of groups.
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
        Closed i _ -> [i]
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
            M.Ret _ -> ([instr], basic : list)
            M.Error _ -> ([instr], basic : list)
            _ -> (instr : basic, list)

type MLabelMap = Map M.Label Label

-- | Converts a group to a graph. Maintains a dictionary which maps
-- Machine labels to Hoopl labels.
codesToBody :: C.Group -- ^ The group's entry label.
            -> MLabelMap 
            -> FuelMonad (MLabelMap, AGraph InstrNode C C)
codesToBody (groupLabel, groupCount, codes) lbls = do
    entry <- freshLabel
    codesToBody' lbls entry codes
  where
      codesToBody' :: MLabelMap -> Label -> [C.Code] -> FuelMonad (MLabelMap, AGraph InstrNode C C)
      codesToBody' lbls entryL ((entry, instrs):rest) 
          | null instrs = error "TODO: empty code block"
          | null rest = do
              mkGraph (error "Graph should not end with FailT!") 
          | otherwise = do
              nextL <- freshLabel
              (lbls', graph) <- mkGraph nextL
              (lbls'', graph') <- codesToBody' lbls' nextL rest
              return $ (lbls'', graph <#> graph')
        where
          mkGraph nextL = do
            let first = mkLabel entryL
                middles = map middle (init instrs)
            (lbls', last) <- end (Map.insert entry entryL lbls) nextL (last instrs)
            return $ (lbls', mkFirst first <*> catAGraphs middles <*> mkLast last)
          mkLabel entryL
            | entry == groupLabel = EntryLabel entry groupCount entryL
            | otherwise = LabelNode groupLabel entry entryL
          middle i = case i of 
                       M.Halt -> codeError "Illegal instruction in middle of block."
                       M.Ret _ -> codeError "Illegal instruction in middle of block."
                       M.Jmp _ -> codeError "Illegal instruction in middle of block."
                       M.Error _ -> codeError "Illegal instruction in middle of block."
                       _ -> mkMiddle $ Open i
          end :: MLabelMap -> Label -> M.Instr -> FuelMonad (MLabelMap, InstrNode O C)
          end lbls nextLabel i = do
            case i of
              M.Ret _ -> return (lbls, Ret i)
              M.Jmp l -> do
                     fresh <- freshLabel
                     let (lbls', foundL) = findLabel lbls l fresh
                     return (lbls', Closed i foundL)
              M.Halt -> return (lbls, Halt i)
              M.FailT _ _ l -> do
                     fresh <- freshLabel
                     let (lbls', foundL) = findLabel lbls l fresh
                     return (lbls', FailT i foundL nextLabel)
              M.Error _ -> return (lbls, Error i)
              _ -> codeError "Illegal instruction at end of code block."
          codeError msg = error (msg ++ " " ++ show instrs ++ " " ++ show rest)
          -- Find label associated with l, or associate label l
          -- with the fresh label given.
          findLabel :: MLabelMap -> C.Label -> Label -> (MLabelMap, Label)
          findLabel lbls l fresh = case Map.lookup l lbls of
                                     Just lbl -> (lbls, lbl)
                                     Nothing -> (Map.insert l fresh lbls, fresh)

-- | Retrieve the body of a graph.
bodyOf :: AGraph InstrNode C C -> FuelMonad (Body InstrNode)
bodyOf aGraph = do
  (GMany _ b _) <- graphOfAGraph aGraph
  return b


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
