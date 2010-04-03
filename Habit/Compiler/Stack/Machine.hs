module Habit.Compiler.Stack.Machine

where

import Data.Char (toUpper)
import System.IO.Unsafe (unsafePerformIO)
import System.IO (hFlush, stdout)

data Val = IntV Int -- ^ An integer value.
         | DataV Tag [Val] -- ^ A closure or structured data value
                           -- with fields. Val is a LabelV if this is
                           -- closure, otherwise it is a tag,
                           -- representing a constructor. Fields are
                           -- indexed from 0, at the beginning of the
                           -- list.
         | LitV String -- ^ A literal value.
         deriving (Read, Show, Eq)

-- | A value can be found on the stack or in a field 
-- of a value on the stack. Fields can be nested, so
-- a value inside a structure can be found. 
data Loc = Stack Int -- ^ Value on stack at offset given. Offsets
                     -- start at 0, meaning the BOTTOM of the
                     -- stack, and go up.
         | Field Loc Int -- ^ Field in a value at some location. Field
                         -- offsets start at 0 and go up.
         deriving (Read, Show, Eq)

type Stack a = [a]
type StackV = Stack Val

-- | Number of values a constructor takes
type Arity = Int

-- | Identifies a particular constructor.
type Tag = String

-- | Named location in a program.
type Label = String

-- | Instructions available to the
-- machine
data Instr = Enter -- ^ Use value on top of stack as point to the label for function to jump to
          | Ret -- ^ Return from procedure call. 
          | AllocC Label [Loc] -- ^ Allocate N values with a label. 
          | AllocD Tag Arity -- ^ Allocate data with the tag given and space for the number of arguments. 
          | PushL Loc -- ^ Fetch a value from the location specified to the top of the stack. 
          | Copy Loc Loc -- ^ Copy a value from one location to another. The first argument
                         -- is the source and the second the destination. The value in the destination
                         -- will be replaced.
          | FailT Loc Tag Label -- ^ Jump to the given label if the value in the
                                 -- location specified does NOT match the tag given. Otherwise
                                 -- continue executing.
          | PushV Val -- ^ Push a value onto the stack.
          | Pop -- ^ Pop a value off the stack
          | MatchStart -- ^ Indicates a match with alternatives has started and 
                       -- the machine's state should be preserved in case of failure.
          | MatchFailure -- ^ Indicates a match has failed; abort.
          | MatchEnd -- ^ Indicates a match operation has finished and machine state no
                     -- longer needs to be preserved.
          | Label Label -- ^ Label the next instruction with the name given.
          | Halt -- ^ End execution
          | Jmp Label -- ^ Jump to the label specified.
          | Add -- ^ Add the top two values on the stack together.
          | Mul -- ^ Multiply the top two values on the stack together.
          | Cmp -- ^ Compare the top two values on the stack. Pop them and leave a 0 if they are equal,
                -- otherwise leave a 1.
          | Error String -- ^ Halt and print error.
          | Note String -- ^ No effect - for commenting
  deriving (Show, Read)

data Program = Program [Instr] Instr [Instr]
               deriving Show

data Machine = Machine { programC :: Program
                       , workStack :: StackV -- ^ Stack is indexed from
                                            -- 0, at the end of the
                                            -- list.
                       , callStack :: [(SP, StackV, Program)]
                       , stackLoc :: SP -- ^ SP is the top of the
                                        -- stack.  SP represents the
                                        -- next empty slot and starts
                                        -- at 0. The 0 position is
                                        -- also the end of the list.
                       , matchStack :: Stack (SP, StackV, [(SP, StackV, Program)])
                       }
               deriving Show

-- | Stack top index.
type SP = Int

runMachine :: [Instr] -> [Machine]
runMachine prog = untilHalt . newMachine $ prog
    where
      untilHalt machine@(Machine { programC = (Program _ Halt _) })
          = [machine]
      untilHalt machine@(Machine { programC = (Program _ (Error _) _) })
          = [machine]
      untilHalt machine@(Machine { programC = (Program _ instr _) })
          = machine : untilHalt (step instr machine)

newMachine (i:is) = Machine (Program [] i is) [] [] 0 []

{-|
 Enter | programC | workStack | callStack | stackLoc | matchStack
-------------------------------------------------
In  | [*i_k*]     | (DataV l ..)_(sb + sp - 1) : ws | cs                       | sp | ..
Out | [*Label l*] | (DataV l ..)_(sb + sp - 1) : ws | (sp, ws, *i_(k+1)*) : cs | 2  | ..

 Ret | programC | workStack | callStack | stackLoc | stackLoc | matchStack
-------------------------------------------------
In   | ..      | v : ..  | (sp', ws, *i_k*) : cs | sp      | ..
Out  | [*i_k*] | v : ws  | cs                    | sp' - 1 | ..

 AllocC l m | programC | workStack | callStack | stackLoc | matchStack
-------------------------------------------------
In   | ..            | ws                           | .. | sp | ..
Out  | ..            | (DataV l c_0 .. c_m)_st : ws | .. | sp + 1 | ..

 AllocD tag m | programC | workStack | callStack | stackLoc | matchStack
-------------------------------------------------
In   | ..            | ws                          | .. | sp | ..
Out  | ..            | (DataV tag v_0 .. v_m) : ws | .. | sp + 1 | ..

 PushL l | programC | workStack | callStack | stackLoc | matchStack
-------------------------------------------------
In   | .. | .. ws_l .. ws           | .. | sp | ..
Out  | .. | ws[l] : .. ws_l ..  ws  | .. | sp + 1 | ..

 Copy l1 l2 | programC | workStack | callStack | stackLoc | matchStack
-------------------------------------------------
In   | .. | .. ws_l2 .. ws_l1 : ws  | .. | sp | ..
Out  | .. | .. ws_l1 .. ws_l1 : ws  | .. | sp | ..

 FailT l t lab | programC | workStack | callStack | stackLoc | matchStack
-------------------------------------------------
In   | .. *i_n* ..      | .. (DataV t ..)_l : ws | .. | .. | ..
Out  | .. *i_(n+1) * .. | .. (DataV t ..)_l : ws | .. | .. | ..

 FailT l t lab | programC | workStack | callStack | stackLoc | matchStack
-------------------------------------------------
In   | .. *i_n* ..         | .. (DataV n ..)_l : ws | .. | .. | ..
Out  | .. *(Label lab)* .. | .. (DataV n ..)_l : ws | .. | .. | ..

 PushV v | programC | workStack | callStack | stackLoc | matchStack
-------------------------------------------------
In   | .. | ws     | .. | sp | ..
Out  | .. | v : ws | .. | sp + 1 | ..

 Pop | programC | workStack | callStack | stackLoc | matchStack
-------------------------------------------------
In   | .. | v : ws | .. | sp | ..
Out  | .. | ws     | .. | sp - 1 | ..

 MatchStart | programC | workStack | callStack | stackLoc | matchStack
-------------------------------------------------
In   | .. | ws | css | sp | mss
Out  | .. | ws | ..  | .. | (sp, ws, css) : mss

 MatchFailure | programC | workStack | callStack | stackLoc | matchStack
-------------------------------------------------
In   | .. | ws' | css' | sp' | (sp, ws, css) : mss
Out  | .. | ws  | css  | sp  | mss

 MatchEnd | programC | workStack | callStack | stackLoc | matchStack
-------------------------------------------------
In   | .. | .. | .. | .. | ms : mss
Out  | .. | .. | .. | .. | mss

-}
step :: Instr -> Machine -> Machine
step Enter machine@(Machine { programC = pC
                            , workStack = (clo@(DataV l _) : arg : ws)
                            , callStack = cs
                            , stackLoc = sp })
    = case findLabel pC l of
        Just pC' -> machine { programC = pC'
                            , callStack = (sp, ws, nextInstr pC) : cs
                            , workStack = [clo, arg]
                            , stackLoc = 2 }
        _ -> err machine $ "Can't find label " ++ l ++ " for Enter in machine " ++ showMachine machine
step Enter machine = err machine $ "Illegal state for Enter: " ++ showMachine machine
step Ret machine@(Machine  { workStack = (w:_)
                           , callStack = (sp', ws, cs) : css
                           , stackLoc = sp })
    = machine { programC = cs
              , workStack = (w : ws)
              , callStack = css
              , stackLoc = sp' - 1 }
step Ret machine = err machine $ "Illegal state for Ret: " ++ showMachine machine
step (AllocC l locs) machine@(Machine { workStack = ws
                                      , stackLoc = sp })
    = let findSafe (Field s o) = getField (findSafe s) o
          -- A closure may refer to itself (especially if the function
          -- is recursive. Therefore, when we access the values
          -- we special case for a stack location that is equal to sp,
          -- the top of the stack. That location means we are referring to 
          -- the value we are building now. Otherwise, go find the value using the
          -- normal findVal function.
          findSafe (Stack i) 
            | i == sp = v
            | otherwise = findVal ws sp (Stack i)
          v = DataV l (map findSafe locs)
      in next $ machine { workStack = v : ws
                        , stackLoc = sp + 1 }
step (AllocD t m) machine@(Machine { workStack = ws
                                   , stackLoc = sp })
    = next $ machine { workStack = (DataV t . replicate m $ IntV 0) : ws
                     , stackLoc = sp + 1 }
step (PushL l) machine@(Machine { workStack = ws
                                , stackLoc = sp })
    = next $ machine { workStack = findVal ws sp l : ws
                     , stackLoc = sp + 1 }
step (Copy src dst) machine@(Machine { workStack = ws 
                                     , stackLoc = sp }) 
    = update (findVal ws sp src) 
  where
    update v = maybe err2 done 
                 (setLoc ws sp dst v) 
    done ws' = next $ machine { workStack = ws' }
    err1 = err machine $ "Can't find value for Copy (" ++ show src ++ "): " ++ showMachine machine
    err2 = err machine $ "Can't set value for Copy (" ++ show dst ++ "): " ++ showMachine machine
step (FailT loc t1 lab) machine@(Machine { programC = pC
                                         , workStack = ws 
                                         , stackLoc = sp })
    = check (findVal ws sp loc)
  where
    check (DataV t2 _) 
        | t2 == t1 = next machine -- Tag matches, continue
        | otherwise = maybe err2 done (findLabel pC lab)
    check _ = err machine $ "Illegal state for FailT: " ++ showMachine machine
     -- match failure
    done pC' = machine { programC = pC' }
    err1 = err machine $ "Loc " ++ show loc ++ " given for FailT is invalid: " ++ showMachine machine
    err2 = err machine $ "Can't find label " ++ lab ++ " for FailT in machine " ++ showMachine machine

step (PushV v) machine@(Machine { workStack = ws
                                , stackLoc = sp })
    = next $ machine { workStack = v : ws
                     , stackLoc = sp + 1 }

step Pop machine@(Machine { workStack = v : ws
                          , stackLoc = sp })
    = next $ machine { workStack = ws
                     , stackLoc = sp - 1 }
step Pop machine = err machine $ "Illegal state for Pop: " ++ showMachine machine

step MatchStart machine@(Machine { workStack = ws
                                 , callStack = css
                                 , stackLoc = sp
                                 , matchStack = mss })
    = next $ machine { matchStack = (sp, ws, css) : mss }

step MatchFailure machine@(Machine { matchStack = (sp, ws, css) : mss })
    = next $ machine { workStack = ws
                     , callStack = css
                     , stackLoc = sp
                     , matchStack = mss }
step MatchFailure machine = err machine $ "Top level matching failure."

step MatchEnd machine@(Machine { matchStack = ms : mss })
   = next $ machine { matchStack = mss }
step MatchEnd machine = err machine $ "Illegal state for MatchEnd: " ++ showMachine machine

step (Label _) machine = next machine 
step Halt machine = machine 

step (Jmp l) machine@(Machine { programC = pC })
    = case findLabel pC l of
        Just pC' -> machine { programC = pC' }
        _ -> err machine $ "Can't find label " ++ l ++ " for Jmp in machine " ++ showMachine machine

step Add machine@(Machine { workStack = (IntV v1) : (IntV v2) : ws
                          , stackLoc = sp })
    = next $ machine { workStack = (IntV (v1 + v2)) : ws
                     , stackLoc = sp - 1 }
step Add machine = err machine $ "Illegal state for Add: " ++ showMachine machine
step Mul machine@(Machine { workStack = (IntV v1) : (IntV v2) : ws
                          , stackLoc = sp })
    = next $ machine { workStack = (IntV (v1 * v2)) : ws 
                     , stackLoc = sp - 1 }
step Mul machine = err machine $ "Illegal state for Mul: " ++ showMachine machine
step Cmp machine@(Machine { workStack = (IntV t1) : (IntV t2) : ws 
                          , stackLoc = sp })
    = next $ 
       if t1 == t2
        then machine { workStack = (IntV 0) : ws
                     , stackLoc = sp + 1  }
        else machine { workStack = (IntV 1) : ws 
                     , stackLoc = sp + 1 }
step Cmp machine = err machine $ "Illegal state for Cmp: " ++ showMachine machine

step (Error msg) machine = machine 
step (Note _) machine = next machine

-- | Advance to next instruction. Error if we are at the end
-- of the program.
next :: Machine -> Machine
next machine@(Machine { programC = pc}) = machine { programC = nextInstr pc} 

-- | Put machine into error state.
err :: Machine -> String -> Machine
err machine@(Machine { programC = (Program prev i rest) }) str 
    = machine { programC = Program prev (Error str) (i:rest) }

-- | Advance a program one instruction
nextInstr :: Program -> Program
nextInstr (Program _ _ []) = error "Can't advance to next instruction!"
nextInstr (Program li i (r:ri)) = Program (li ++ [i]) r ri

-- | Advance to previous instruction. Error if we are at the beginning
-- of the program.
prevInstr :: Program -> Program
prevInstr (Program [] _ _) = error "Can't advance to previous instruction!"
prevInstr (Program ps c rs) = Program (init ps) (last ps) (c:rs)

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
    isLabel instr@(Program _ (Label l) _) = l == label
    isLabel _ = False
    -- | Check if we are at the end of the program.
    atEnd :: Program -> Bool
    atEnd (Program _ _ []) = True
    atEnd _ = False
    -- | Check if we are at the beginning.
    atBegin :: Program -> Bool
    atBegin (Program [] _ _) = True
    atBegin _ = False

-- | Find a value on the stack, in the location
-- given. The location is relative to the current
-- base pointer, but we only need to know the top
-- of the stack to find it.
findVal :: StackV -> SP -> Loc -> Val
findVal stack sp (Stack idx) 
    = head . snd . splitStack stack sp $ idx
findVal stack sp (Field l o) 
    = getField (findVal stack sp l) o
{-
findVal :: StackV -> SP -> Loc -> Maybe Val
findVal stack sp (Stack idx) 
    | idx >= sp = Nothing
    | otherwise = 
        let (s0, s1) = splitStack stack sp idx
        in if null s1 
            then Nothing
            else Just (head s1)
findVal stack sp (Field l o) = do
  val <- findVal stack sp l
  getField val o
-}

-- | Set the location specified to the value
-- given. The previous value is replaced. If
-- the location given is invalid, Nothing
-- is returned. Otherwise, the new stack
-- is returned.
setLoc :: StackV -> SP -- ^ Our stack is indexed from the base pointer, but
                      -- we don't need it here. SP represents the top
                      -- of the stack, so we can use it with Loc 
                      -- to determine what element to retrieve.
       -> Loc -> Val -> Maybe StackV 
setLoc stack sp (Stack idx) v 
    | idx >= sp = Nothing
    | otherwise = 
        let (s0, s1) = splitStack stack sp idx
        in Just (s0 ++ v : drop 1 s1)
setLoc stack sp (Field l o) v = do
    let old = findVal stack sp l
    new <- setField v old o
    setLoc stack sp l new

-- | Set a field in a DataV structure.
setField :: Val -- ^ New value
         -> Val -- ^ DataV structure to update
         -> Int  -- ^ Offset of field in structure. Indexed by 0.
         -> Maybe Val
setField v (DataV t fields) o 
    | length fields > o && o >= 0 =
        let (f0, f1) = splitAt o fields
        in Just . DataV t $ f0 ++ v : drop 1 f1
    | otherwise = Nothing
setField _ _ _ = Nothing

-- | Get a field from a DataV structure.
getField :: Val -> Int -> Val
getField (DataV l fields ) o = head . drop o $ fields

{- 
getField :: Val -> Int -> Maybe Val
getField (DataV _ fields ) o 
    | (length fields) >= o = Just . head . drop o $ fields
    | otherwise = Nothing
getField _ _ = Nothing
-}

-- | Helper function which takes a stack location
-- and opens a hole up for us. The value at the index
-- given will be the first value in the second list
-- of the tuple.
splitStack stack sp idx = splitAt (sp - idx - 1) stack

showMachine :: Machine -> String
showMachine (Machine { programC = pc
                     , workStack = ws
                     , callStack = cs
                     , stackLoc = sp })
    = "PC: " ++ showProg pc ++ ", WS: " ++
      show (length ws) ++ ", CS: " ++ show (map showCS cs) ++
      ", SP: " ++ show sp

showCS (sp, ws, prog) = "(" ++ show sp ++ ", " ++ show (length ws) ++ 
                         ", " ++ showProg prog ++ ")"

showProgs [] = "[]"
showProgs (c:_) = showProg c

showProg (Program _ i _) = "_ " ++ show i ++ " _ "

showVals :: [Val] -> String
showVals [] = "[]"
showVals (w:ws) = foldl (\a b -> a ++ ", " ++ showVal b) (showVal w) ws

showVal (IntV i) = show i
showVal (DataV t vs) = "{" ++ show t ++ ": " ++ showVals vs ++ "}"
showVal (LitV l) = show l

tf :: String -> a -> a
tf msg a = unsafePerformIO $ do
    putStrLn msg
    hFlush stdout
    return a