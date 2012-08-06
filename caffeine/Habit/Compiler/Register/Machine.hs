{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}
module Habit.Compiler.Register.Machine

where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.List (intercalate)
import Data.Maybe (fromJust, fromMaybe, catMaybes)
import Control.Monad (foldM)

-- | A register is just a unique name for
-- a location. 
type Reg = String

-- | A field is referred to by an offset within
-- a particular register. Fields are indexed from 0.
type Field = (Reg, Int)

-- | Well-known argument, closure and final result registers.
argReg, cloReg, resultReg :: Reg
cloReg = "clo"
argReg = "arg"
resultReg = "result"

newtype Failure = F Label
  deriving (Eq, Read, Show)

newtype Success = S Label
  deriving (Eq, Read, Show)

-- | Instructions available to the machine.
data Instr = 
  Enter Reg Reg Reg 
  -- ^ Enter the closure at the first location, with the argument at
  -- the second location.  The result of the Enter will be in the
  -- register in the third location.
  | Ret Reg -- ^ Return from procedure call.
  | MkClo Reg Label [Reg] 
  -- ^ Create a closure using the label given, storing value from the
  -- registers specified. Put the result in the register given.
  | Capture Reg Label Int 
  -- ^ Create a new closure to hold the values found in the closure
  -- and argument registers. The new closure is placed in the register
  -- specified and returned. The count given represents the number of
  -- slots expected in the closure register, which can be zero.
  | AllocD Reg Tag Int 
  -- ^ Allocate data with the tag given and space for the number of
  -- arguments.
  | Copy Reg Reg 
  -- ^ Copy a value from one location to another. The first argument
  -- is the source and the second the destination. The value in the
  -- destination will be replaced.
  | Store Reg Field 
  -- ^ Store the value in a register into the field given. The first
  -- argument is the register to store. The second is the destination
  -- register, with an offset indexed from 0.
  | Load Field Reg  
  -- ^ Load a value from a register and offset into a particular
  -- register. The first argument is the source register, with an
  -- offset indexed from 0. The second argument is the destination
  -- register.
  | Set Reg Val -- ^ Set a register to a value.
  | FailT Reg Tag Failure Success 
  -- ^ Jump to the given label if the value in the location specified
  -- does NOT match the tag given. Otherwise continue executing.
  | Label Label -- ^ Label the next instruction with the name given.
  | Halt -- ^ End execution
  | Jmp Label -- ^ Jump to the label specified.
  | Error String -- ^ Halt and print error.
  | Note String -- ^ No effect - for commenting
  deriving (Show, Read)

-- | Identifies a particular constructor.
type Tag = String

-- | Marks a named location in the program. Entry
-- additionally means the location is the entry point
-- for a function. 
type Label = String

-- | Values the machine can represent.
data Val = Num Int -- ^ An integer value.
         | Data Tag [Val] -- ^ A closure or structured data value
                           -- with fields. Val is a LabelV if this is
                           -- closure, otherwise it is a tag,
                           -- representing a constructor. Fields are
                           -- indexed from 0, at the beginning of the
                           -- list.
         | Str String -- ^ A literal value.
         deriving (Read, Show, Eq)

-- | Represents the machine's current state.
data Machine = Machine { program :: Program
                       , registers :: Registers
                       , callStack :: Stack (Registers, Reg, Program) }
               deriving Show

type Registers = Map String Val

-- | A program is a sequence of instructions, with the 
-- instruction currently executing at the "focus."
data Program = Program [Instr] Instr [Instr]
               deriving Show

-- | Execute a sequence of instructions and produce
-- the successive machine states. Execution terminates
-- when a Halt or Error instruction is seen.
runMachine :: [Instr] -> [Machine]
runMachine prog = untilHalt . newMachine $ prog
    where
      -- Halt on error, Halt, or when a return with no call stack
      -- is encountered.
      untilHalt machine@(Machine { program = (Program _ Halt _) })
          = [machine]
      untilHalt machine@(Machine { program = (Program _ (Error _) _) })
          = [machine]
      untilHalt machine@(Machine { program = (Program _ (Ret _) _)
                                 , callStack = [] })
          = [machine]
      untilHalt machine@(Machine { program = (Program _ instr _) })
          = machine : untilHalt (step instr machine)
      newMachine (i:is) = Machine (Program [] i is) Map.empty []

-- | Step the machine from its current state to the next, based
-- on the instruction given.
step :: Instr -> Machine -> Machine

-- (Enter r1 r2 r3) | program | registers | callStack 
-------------------------------------------------
-- In               | [*i_k*]     | r1[0] == (DataV l ..) | cs
-- Out              | [*Label l*] | clo = r1, arg = r2    | (r3, [*i_k*]) : cs
step (Enter r1 r2 r3) machine@(Machine { program = p
                                       , registers = rs
                                       , callStack = cs })
    = case getRegs of
        Just (clo'@(Data l _), arg') ->
            case findLabel p l of
              Just p' -> machine { program = p'
                                 , registers = setRegister cloReg clo' . 
                                               setRegister argReg arg' $ rs
                                 , callStack = (rs, r3, (nextInstr p)) : cs }
              _ -> err machine $ "Label " ++ show l ++ " not found."
               
        _ -> err machine $ "Register " ++ r1 ++ " is not a closure because it does not contain the appropriate value."
      where
        getRegs = do
          clo' <- getRegister rs r1
          arg' <- getRegister rs r2
          return (clo', arg')
        
-- Ret r | program | registers | callStack 
-------------------------------------------------
-- In   | p  | ...     | (dst, p') : cs 
-- Out  | p' | dst = r | cs
step (Ret r) machine@(Machine { registers = rs'
                              , callStack = (rs, dst, p') : cs })
    = case getRegister rs' r of
        Just v -> machine { program = p'
                          , registers = setRegister dst v rs
                          , callStack = cs }
        _ -> err machine $ "Can't get value for result register " ++ r ++ " in " ++ show rs'
step (Ret _) machine = err machine $ "Illegal state for Ret."

-- MkClo r lab rs_n | program | registers | callStack 
-------------------------------------------------
-- In   | ... | v0 = rs[0], v1 = rs[1], ..., vq = rs[n - 1] | cs 
-- Out  | ... | r = Data lab [v0, v1, ..., vq, vn]           | cs
step (MkClo reg lab regs) machine@(Machine { registers = rs }) = 
  let initV = mkData lab (length regs)
      cloM = do
        regsV <- mapM (getRegister rs) regs
        foldM (\v (idx, r) -> setField r v idx) initV (zip [0..] regsV)
      closureV = mightErr "Unable to make closure." cloM
  in next $ machine { registers = setRegister reg closureV rs }

-- Capture r lab n | program | registers | callStack 
-------------------------------------------------
-- In   | p  | v0 = clo[0], v1 = clo[1], ..., v_(n-1) = clo[n-1], v_n = arg | (dst, p') : cs 
-- Out  | p' | dst = r = Data lab [v0, v1, ..., v_n] | cs
step (Capture _ lab cnt) machine@(Machine { registers = rs'
                                          , callStack = (rs, dst, p') : cs }) = 
  let initV = mkData lab (cnt + 1)
      cloV = mightErr "Could not get closure register in Capture." $ getRegister rs' cloReg
      argV = mightErr "Could not get argument register in Capture." $ getRegister rs' argReg 
      cloFs = catMaybes . map (getField cloV) $ [0..cnt - 1]
      valM = do
        intrmM <- foldM (\v (idx, fv) -> setField fv v idx) initV (zip [0..] cloFs)
        setField argV intrmM cnt
      valV = mightErr "Unable to capture closure." $ valM
  in machine { program = p'
             , registers = setRegister dst valV rs
             , callStack = cs }
step (Capture _ _ _) machine = err machine "Illegal state for Capture."

-- AllocD r t n | program | registers | callStack 
-------------------------------------------------
-- In   | ... | ...                    | cs 
-- Out  | ... | r = Data t [0, 0, ..]  | cs
step (AllocD reg tag amt) machine@(Machine { registers = rs }) = 
  next $ machine { registers = setRegister reg (mkData tag amt) rs }

-- Copy src dst | program | registers | callStack 
-------------------------------------------------
-- In   | ... | src = v | cs 
-- Out  | ... | dst = v | cs
step (Copy src dst) machine@(Machine { registers = rs }) 
    = case getRegister rs src of
        Just v -> next $ machine { registers = setRegister dst v rs }
        _ -> err machine $ "Can't find src reg for Copy (" ++ src ++ ")."

-- Store src (dst, i) | program | registers | callStack 
-------------------------------------------------
-- In   | ... | src = v    | cs 
-- Out  | ... | dst[i] = v | cs
step (Store src (dst, i)) machine@(Machine { registers = rs }) 
    = case (getRegister rs src, getRegister rs dst) of
        (Just v, Just d) -> 
            case setField v d i of
              Just d' -> 
                  next $ machine { registers = setRegister dst d' rs }
              _ -> err machine $ "Unable to store value to (" ++ dst ++ ", " ++ 
                     show i ++ "). "
        _ -> err machine $ "Unable to get value from " ++ src ++ "."

-- Load (src, i) dst | program | registers | callStack 
-------------------------------------------------
-- In   | ... | v = dst[i] | cs 
-- Out  | ... | dst = v    | cs

step (Load (src, i) dst) machine@(Machine { registers = rs }) 
     = case getRegister rs src of
         Just d -> 
             case getField d i of
               Just v -> next $ machine { registers = setRegister dst v rs }
               _ -> err machine $ "Unable to get field " ++ show i ++ " from " ++ src
         _ -> err machine $ "Unable to get register " ++ src

-- Set dst v | program | registers | callStack 
-------------------------------------------------
-- In   | ... | ...     | cs 
-- Out  | ... | dst = v | cs
step (Set dst v) machine@(Machine { registers = rs })
    = next $ machine { registers = setRegister dst v rs }

-- FailT reg t1 f s | program | registers | callStack 
-------------------------------------------------
-- In   | [*i_k*]   | (Data t1 _) == reg | cs 
-- Out  | [*Label s*] | ...                 | cs

-- FailT reg t1 l | program | registers | callStack 
-------------------------------------------------
-- In   | [*i_k*]     | (Data t2 _) == reg | cs 
-- Out  | [*Label f*] | ...                | cs

step (FailT reg t1 (F f) (S s)) machine@(Machine { program = p
                                       , registers = rs })
    = case getRegister rs reg of
        (Just (Data t2 _)) 
           | t2 == t1 -> maybe (err1 s) jump (findLabel p s) -- Tag matches, continue
           | otherwise -> maybe (err1 f) jump (findLabel p f)
        _ -> err machine $ "Illegal state for FailT."
  where
    jump p' = machine { program = p' }
    err1 l = err machine $ "Can't find label " ++ l ++ " for FailT in machine."

step (Label _) machine = next machine 
step Halt machine = machine 

step (Jmp l) machine@(Machine { program = p })
    = case findLabel p l of
        Just p' -> machine { program = p' }
        _ -> err machine $ "Can't find label " ++ l ++ " for Jmp."

step (Error _) machine = machine 
step (Note _) machine = next machine

-- | Advance to next instruction. 
next :: Machine -> Machine
next machine@(Machine { program = pc}) = machine { program = nextInstr pc} 

-- | Advance a program one instruction
nextInstr :: Program -> Program
nextInstr (Program _ _ []) = error "Can't advance to next instruction!"
nextInstr (Program li i (r:ri)) = Program (li ++ [i]) r ri

-- | Search for the given label in the program. Returns
-- that point in the program, if it is found.
findLabel :: Program -> String -> Maybe Program
findLabel instr label = 
    case (forward instr, backward instr) of
      (Just instr', _)  -> Just instr'
      (_, Just instr') -> Just instr'
      _ -> Nothing
  where
    forward instr = 
        case (isLabel instr, atEnd instr) of
          (True, _) -> Just instr
          (_, True) -> Nothing
          _ -> forward (nextInstr instr)
    backward instr = 
        case (isLabel instr, atBegin instr) of
          (True, _) -> Just instr
          (_, True) -> Nothing
          _ -> backward (prevInstr instr)
    isLabel (Program _ (Label l) _) = l == label
    isLabel _ = False
    -- | Check if we are at the end of the program.
    atEnd :: Program -> Bool
    atEnd (Program _ _ []) = True
    atEnd _ = False
    -- | Check if we are at the beginning.
    atBegin :: Program -> Bool
    atBegin (Program [] _ _) = True
    atBegin _ = False
    prevInstr (Program [] _ _) = error "Can't advance to previous instruction!"
    prevInstr (Program ps c rs) = Program (init ps) (last ps) (c:rs)

-- | Put machine into error state.
err :: Machine -> String -> Machine
err machine@(Machine { program = (Program prev i rest) }) str 
    = machine { program = Program prev 
                          (Error $ str ++ showMachine machine) 
                          (i:rest) }

-- | Create a data value with the tag given and
-- number of fields specified. All fields are 
-- initialized to -1.
mkData tag amt = Data tag . replicate amt $ Num (-1)

-- | Get the value of a register, if the register exists.
getRegister :: Registers -> Reg -> Maybe Val
getRegister registers r = Map.lookup r registers

-- | Set a register to a particular value.
setRegister :: Reg -> Val -> Registers -> Registers
setRegister r v registers = Map.insert r v registers

-- | Set a field in a Data structure.
setField :: Val -- ^ New value
         -> Val -- ^ DataV structure to update
         -> Int  -- ^ Offset of field in structure. Indexed by 0.
         -> Maybe Val
setField v (Data t fields) o 
    | length fields > o && o >= 0 =
        let (f0, f1) = splitAt o fields
        in Just . Data t $ f0 ++ v : drop 1 f1
    | otherwise = Nothing
setField _ _ _ = Nothing

-- | Get a field from a Data structure.
getField :: Val -> Int -> Maybe Val
getField (Data l fields) o =
    case drop o fields of
      (v:_) -> Just v
      _ -> Nothing

showMachine :: Machine -> String
showMachine (Machine { program = p
                     , registers = regs
                     , callStack = cs })
    = "PC: " ++ showProg p ++ ", Regs: " ++
      showRegs regs ++ ", CS: " ++ showCS cs

showCS [] = "[]"
showCS ((regs, r, c):_) = "(" ++ show (Map.size regs) ++ "," ++ r ++ ", " ++ showProg c ++ ")"

showProg (Program _ i _) = "_ " ++ show i ++ " _ "

showRegs = intercalate "," . map showReg . Map.toList
showReg (k, v) = k ++ ": " ++ showVal v

showVals :: [Val] -> String
showVals [] = "[]"
showVals (w:ws) = foldl (\a b -> a ++ ", " ++ showVal b) (showVal w) ws

showVal (Num i) = show i
showVal (Data t vs) = "{" ++ t ++ ": " ++ showVals vs ++ "}"
showVal (Str l) = l

mightErr :: String -> Maybe a -> a
mightErr msg = fromMaybe (error msg)

type Stack a = [a]
