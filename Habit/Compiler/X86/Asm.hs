{-# LANGUAGE CPP #-}
module Habit.Compiler.X86.Asm 

where

import System.Info (os)

type Op = String
type Reg = String
newtype Label = Label String

-- | Locations where temporaries can be found.
data Loc = O Int -- ^ An offset from EBP
         | L String -- ^ A fixed label.
         | G String -- ^ A global label.
         | R Reg -- ^ A register.
  deriving (Eq, Show)

newtype Ref = Ref Loc -- ^ For constructing refernces to locations.

-- | Convert a value to immediate value source rep.
immd l = toVal l

-- | A null-terminated string literal, declared in the __data section.
asciz s = spc ++ ".asciz " ++ show s

-- | Declare the given label as a global.
globl l = spc ++ ".globl " ++ toVal l

-- | Add a comment to the output.
comment instr = spc ++ "# " ++ show instr

-- | EAX register.
eax = R "eax"
-- | EBP register.
ebp = R "ebp"
-- | EBX register.
ebx = R "ebx"
-- | ECX register.
ecx = R "ecx"
-- | EDI register.
edi = R "edi"
-- | EDX register.
edx = R "edx"
-- | ESI register.
esi = R "esi"
-- | ESP register.
esp = R "esp"

addl a b = spc ++ "addl " ++ toLoc a ++ ", " ++ toLoc b

call dest = spc ++ "call " ++ toTarget dest

cmpl a b = spc ++ "cmpl " ++ toLoc a ++ ", " ++ toLoc b

jmp l = spc ++ "jmp " ++ toVal l

jecxz l = spc ++ "jecxz " ++ toVal l

jnz l = spc ++ "jnz " ++ toVal l

-- | Labeled location.
label l = l ++ ":"

-- | Label with a value.
labelL l v = l ++ ":" ++ " .long " ++ toVal v

long i = spc ++ ".long " ++ toVal i

movl a b = spc ++ "movl " ++ toLoc a ++ ", " ++ toLoc b

nop instr = spc ++ "nop # " ++ show instr

popl a = spc ++ "popl " ++ toLoc a

pushl a = spc ++ "pushl " ++ toLoc a

ret = spc ++ "ret"

subl a b = spc ++ "subl " ++ toLoc a ++ ", " ++ toLoc b

spc = concat . replicate 4 $ " "

-- | OS specific external labels.
mkExternLabel l = 
    let osPrefix "linux" = ""
        osPrefix "mingw32" = "_"
        osPrefix "darwin" = "_"
        osPrefix o = error $ "Unknown OS " ++ o
    in osPrefix os ++ l 

class ToLocation a where
    toLoc :: a -> String

class ToValue a where
    toVal :: a -> String

class ToLiteral a where
    toLiteral :: a -> String

class ToTarget a where
    toTarget :: a -> String
