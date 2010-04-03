> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts
>   , CPP #-}
> module Habit.Compiler.X86.Compiler

This module handles conversion from Register machine instructions
to x86 assembly code.

> where
>
> import Data.List (nub, (\\), isPrefixOf, partition)
> import Data.Maybe (isJust)
> import Control.Monad
> import Control.Monad.Writer
> import Control.Monad.State
> import Data.Map (Map)
> import qualified Data.Map as Map
> import Data.Supply
> import Numeric (showHex)

> import Habit.Compiler.Register.Machine (Instr(..), Reg , Field, Tag)
> import qualified Habit.Compiler.Register.Machine as H
> import Habit.Compiler.Register.Compiler (Group, Code)
> import Habit.Compiler.X86.Asm hiding (Label)
> import qualified Habit.Compiler.X86.Asm as A
> import Debug.Trace 

Our core function generates code for a given instruction. Some
conventions need to be established:

  * The heap will be managed by a call to "alloc", an external
    function. Alloc takes one argument, an address. It returns the
    location of the allocated value, and the address passed will be in
    the first word. Alloc will look at the word preceding the address
    to determine the # of words to allocate (plus one for the
    address).

  * Labels generated will be based on source names, but have an
    illegal character such as '$' prefixed.

  * All values will be stored indirectly in the heap, even immediate
    values.

In the Machine language, all locations are called "Registers." Here,
we call them temporaries and "registers" refers to real machine
registers.

Our environment for assembly maps temporaries to an offset
from EBP, a fixed location, or a register.

> type Name = String
> type Env = [(Name, Loc)] 
> type Program = [Op]
> type Section = String

C is our assembly compiler. We write labeled blocks of assembler.

> type C = StateT S (Writer [(Section, Either [Op] (String, [Op]))])
> type C' = Writer [Op]
> data S = S { nextLabel :: Supply Int }

To assemble our program, we pass all the function definitions to
assembly and get back a string.

> assemble :: Supply Int -> [Group] -> Program
> assemble supply groups = 
>   let result = execWriter (evalStateT (foldM asmGroup [] groups) (S supply))
>       sections = Map.toList . foldr gather Map.empty $ result
>       gather (s, Left ops) ss = 
>           Map.insertWith (++) s ops ss
>       gather (s, Right (_, ops)) ss = 
>           Map.insertWith (++) s ops ss
>   in concatMap (\(s, ops) -> s : ops) sections

We compile each group individually, using the environment given. We return 
the environment given, plus any new global locations (i.e., labels) emitted.

> asmGroup :: Env -> Group -> C Env
> asmGroup env group@(l, size, ((_, init):rest)) = do

We first find all global declarations in the group.

>     let globals = map (\g -> (g, G g)) (getGlobals group \\ map fst env)

Every function gets a closure and a single argument. By convention,
those are in EDI and ESI. We add these to our environment, plus any
globals we have found.

>         env' = (H.cloReg, edi) : (H.argReg, esi) : globals ++ env

Finally, we extract all temporaries and assign locations on the local
stack.

>         tmps = zipWith (\r i -> (r, O i)) (getTemporaries group \\ map fst env') [0..]

Before any code is written, we create slots in the .data section for any
globals that appear in the group.

>     _data $ do
>       mapM ((\(G g) -> emit $ labelL g (int 0)) . snd) globals

The first code block is always our entry point, which will contain our
'prelude'. Every group starts with the size of the closure it expects,
followed by the entry point label and code to set our stack up.

>     _text $ do 
>       -- HACK: special case for top-level function.
>       case l of
>         "TOP" -> do
>              note "TOP"
>              emit $ globl (mkExternLabel l)
>              emit $ long (int 0) -- Not a data value
>              emit $ long size
>              emit $ label (mkExternLabel l)
>         _     -> do
>              note l
>              emit $ long (int 0) -- Not a data value
>              emit $ long size
>              emit $ label l
>       emit $ pushl ebp
>       emit $ movl esp ebp 

Our stack has the following structure, where addresses increase from
right to left. The address in EBP is at the far left of the diagram.

   old EBP | ret addr | ...

Now we make room for all possible temporaries in the group and update
the environment accordingly. 

>       emit $ subl (word $ length tmps) esp
>       note $ "Made room for " ++ show tmps

Our 'prelude' is finished, so we compile the rest of the instructions in this
group. Since the remaining code blocks are not special, we concatenate all of
them into a list of instructions with appropriate labels. We can then put the
rest of the instructions for this entry point at the front and emit assembler
for the whole list at once. Notice we start with our stack at 0, meaning no
temporaries have been allocated:

>     env'' <- foldM asmInstr (env' ++ tmps) (init ++ toInstrs rest)

The result of our compilation is an environment containing new globals
and the location of any temporaries in the group. We filter out
everything but the globals created.

>     return $ filter (isGlobal . fst) env''
>  where
>     toInstrs :: [Code] -> [Instr]
>     toInstrs = concatMap (\(l, instrs) -> H.Label l : instrs)


Now we emit assembly for each type of instruction. Note that we track the 
stack height in terms of words, so a stack size of 1 means 4 bytes of memory.

> asmInstr :: Env -> Instr -> C Env
> asmInstr env i@(Load (source, idx) dest) = _text $ do
>     note (show i)

To load a value from a field to a destination, we first
find the source location in the environment, then calculate the index offset in bytes, and
finally determine if the destination exists yet. 

>     let sourceLoc = findL source env

We start by move source value to a scratch register and then
move the data to its destination.

>     case sourceLoc of
>       (O i) -> do
>         emit $ movl sourceLoc edx
>         emit $ movl (idx, edx) edx
>       (G l) -> do
>         emit $ movl sourceLoc edx
>         emit $ movl (idx, edx) edx
>       _ -> emit $ movl (idx, sourceLoc) edx
>     store env edx dest 

> asmInstr env i@(Store source (dest, idx)) = _text $ do
>     note (show i)

To store a value, we first move the value from the source location
into a scratch register. We then move the value to the destination. The
stack height and environment are returned unchanged.

>     let sourceL = findL source env
>         destL = findL dest env
>     emit $ movl sourceL edx
>     case destL of
>       (O i) -> do 
>         emit $ movl destL ecx
>         emit $ movl edx (idx, ecx)
>       (G i) -> do 
>         emit $ movl destL ecx
>         emit $ movl edx (idx, ecx)
>       _ -> emit $ movl edx (idx, destL)
>     return env

> asmInstr env i@(Enter closure arg result) = _text $ do 
>     note (show i)

Enter is effectively a procedure call. By convention, EDI holds the
closure and ESI the argument. We save the current closure and argument
on the stack and copy the temporaries specified into EDI and ESI. The
procedure is entered and on return, we restore the previous closure
and argument. The result in EAX is copied into the result temporary.

>     emit $ pushl esi -- arg
>     emit $ pushl edi -- closure
>     let closureL = findL closure env
>         argL = findL arg env
>     emit $ movl closureL edi
>     emit $ movl argL esi
>     emit $ call edi
>     emit $ popl edi -- restore closure
>     emit $ popl esi -- and arg
>     store env eax result

> asmInstr env i@(Ret reg) = _text $ do
>     note (show i)

To return from a function, the temporary given is copied to EAX. ESP
is reset to EBP. EBP is then restored from the stack and a return is
executed.

>     let resultL = findL reg env
>     emit $ movl resultL eax
>     emit $ movl ebp esp
>     emit $ popl ebp
>     emit $ ret
>     return env

> asmInstr env i@(Copy source dest) = _text $ do

Copying one temporary to another uses a scratch register
which does not need to be preserved. A pure language
allows us to share easily, no copying needed! Remember,
all values are indirect so source holds an address, not a
value.

  store source in EDX
  store EDX in dest

>     note (show i)
>     let sourceL= findL source env
>     emit $ movl sourceL edx
>     store env edx dest

> asmInstr env i@(Set reg (H.Str val)) = do
>     l <- newNamedLabel reg
>     _data $ do
>         note (show i)

To set a temporary to a value, we update our environment
to refer to the value.

>         emit $ label l
>         emit $ asciz val
>     return $  (reg, L l) : env

> asmInstr env (Set reg (H.Num val)) = error $ "Can't assemble a numeric value."
> asmInstr env (Set reg (H.Data _ _)) = error $ "Can't assemble a data value."

> asmInstr env i@(FailT reg tag label) = _text $ do
>     let sourceL = findL reg env
>     note $ show i
>     case sourceL of
>       (O i) -> do
>         emit $ movl sourceL ecx
>         emit $ movl (Ref ecx) ecx
>       (G l) -> do
>         emit $ movl sourceL ecx
>         emit $ movl (Ref ecx) ecx
>       _ -> emit $ movl (Ref sourceL) ecx
>     emit $ movl (Ref ecx) ecx
>     emit $ cmpl (hash tag) ecx 
>     emit $ jnz (A.Label label)
>     return env

> asmInstr env i@(Label l) = _text $ do
>     emit $ label l
>     return env

> asmInstr env i@(Halt) = _text $ do
>     emit $ call (mkExternLabel "halt")
>     return env

> asmInstr env i@(Jmp label) = _text $ do
>     emit $ jmp (A.Label label)
>     return env

> asmInstr env i@(Error string) = do
>     l <- newLabel
>     _data $ do
>         emit $ label l
>         emit $ asciz string
>     _text $ do
>         emit $ pushl (A.Label l)
>         emit $ call (mkExternLabel "error")
>     return env

> asmInstr env i@(Note string) = _text $ do
>     return env

> asmInstr env i@(AllocC tmp l 0) = _data $ do
>     note (show i)
>     emit $ labelL tmp (A.Label l)
>     return $ (tmp, L tmp) : env

> asmInstr env i@(AllocC tmp label size) = _text $ do
>     note (show i)
>     allocate env tmp (A.Label label) size

> asmInstr env i@(AllocD tmp tag size) = do
>     let tagL = replace '.' '_' tag
>     env' <- case lookup tag env of
>         Just destL -> return env
>         Nothing -> do
>           l <- newLabel
>           _data $ do
>               note (show i)
>               emit $ label l -- Name of tag
>               emit $ asciz tag
>               emit $ long (A.Label l) -- Address of name
>               emit $ long (int 1) -- Is a data value
>               emit $ long size
>               emit $ labelL tagL (hash tag)
>           return ((tag, L tagL) : env)
>     if (size > 0)
>      then _text $ do
>             note (show i)
>             allocate env' tmp (A.Label tagL) size
>      else _data $ do
>             note (show i) 
>             emit $ labelL tmp (A.Label tagL) 
>             return $ (tmp, L tmp) : env'

If the closure has no data elements, we can create it directly as a
labeled value.

> allocate :: Env -> String -> A.Label -> Int -> C' Env
> allocate env tmp tag size = do
>     let destL = findL tmp env

The RTS function "allocate" is used to create the data value. We
pass it the address (label) which the closure should point to by pushing that
value on the stack. The result is returned in EAX. We push the result to the stack
and associate that location with the temporary in a new environment.

>     emit $ pushl tag
>     emit $ call (mkExternLabel "alloc")
>     emit $ addl (word 1) esp
>     emit $ movl eax destL
>     return $ (tmp, destL) : env

This function take a value and moves it to the destination
location.

> store :: ToLocation a => Env -> a -> Name -> C' Env
> store env val dest = do
>     let destL = findL dest env
>     emit $ movl val destL
>     return env

A magic function that generates a hash code for a given
string. Two identical strings (including case) should always
generate the same hash code. Collisions somewhat likely here. 

> hash :: String -> Int
> hash str = sum . map fromEnum $ str

> isGlobal :: Name -> Bool
> isGlobal name = "glob" `isPrefixOf` name

> findL :: H.Reg -> Env -> Loc
> findL temp env = case lookup temp env of
>   Just l -> l
>   Nothing -> error $ "Can't find " ++ temp ++ " in " ++ show env

Calculating the offset of a value in bytes just assumes
the index given represents the offset in words. We add one
to account for the 'tag' at the beginning of each value.

> offset :: Int -> Int
> offset idx = (idx + 1) * 4

We want to work in words rather than bytes generally, but
assembly likes bytes. This function simply converts word counts
to byte counts.

> word :: Int -> Int
> word count = count  * 4

A convenience function so we don't have to annotate literals.

> int :: Int -> Int
> int i = i

A convenience function for writing a line of source.

> emit :: Op -> C' ()
> emit op = tell [op]

> note :: String -> C' ()
> note s = do
>     emit $ comment s
>     return () 

Write instructions to the .text section.

> _text :: C' a -> C a
> _text action = write ".text" action

Write instructions to the .data section.

> _data :: C' a -> C a
> _data action = write ".data" action

Write instructions to the section specified.

> write :: Section -> C' a -> C a
> write section action = do
>   let (result, ops) = runWriter action
>   tell [(section, Left ops)]
>   return result

> getTemporaries = snd . getRegisters 
> getGlobals = fst . getRegisters
> 

Extract all new registers found in the group and split
them into two lists. The first list holds global registers, while
the second holds local (temporary) registers.

> getRegisters :: Group -> ([H.Reg], [H.Reg])
> getRegisters (_, _, blocks) = partition isGlobal 
>     . nub 
>     . concatMap getReg 
>     . concatMap snd $ blocks
>   where
>     getReg :: H.Instr -> [H.Reg]
>     getReg (H.Enter _ _ r3) = [r3]
>     getReg (H.Ret _) = []
>     getReg (H.AllocC _ _ 0) = []
>     getReg (H.AllocC r1 _ _) = [r1]
>     getReg (H.AllocD r1 _ 0) = []
>     getReg (H.AllocD r1 _ _) = [r1]
>     getReg (H.Copy _ r2) = [r2]
>     getReg (H.Store _ _) = []
>     getReg (H.Load (_, _) r2 ) = [r2]
>     getReg (H.Set r1 _) = [r1]
>     getReg (H.FailT _ _ _) = []
>     getReg _ = []

> -- | Create a unique label.
> newLabel :: C String
> newLabel = do
>     (s1, s2) <- gets (split2 . nextLabel) >>= return
>     put (S s2)
>     -- As long as no one else generates labels that start
>     -- with "L", we are OK.
>     return $ "L" ++ show (supplyValue s1)

> -- | Create a unique label with the given name embedded.
> newNamedLabel :: String -> C String
> newNamedLabel name = do
>     (s1, s2) <- gets (split2 . nextLabel) >>= return
>     put (S s2)
>     return $ "L" ++ (replace '.' '_' name) ++ show (supplyValue s1)

> replace a b ls = 
>     let rep x
>             | x == a = b
>             | otherwise = x
>     in map rep ls

> instance ToLocation (Int, Loc) where
>     toLoc (idx, O s) = error $ "Can't de-ref stack location and add index."
>     toLoc (idx, G l) = error $ "Can't de-ref global location and add index."
>     toLoc (idx, L l) = show (offset idx) ++ "($" ++ l ++ ")"
>     toLoc (idx, R reg) = show (offset idx) ++ "(%" ++ reg ++ ")"

> instance ToLocation Loc where
>     toLoc (O s) = show (negate $ word (s + 1)) ++ "(%ebp)"
>     toLoc (L l) = "$" ++ l
>     toLoc (R reg) = "%" ++ reg
>     toLoc (G l) = l

> instance ToLocation A.Label where
>     -- Bit of a hack here to ensure we 
>     -- move the address onto the stack when
>     -- calling alloc; Unsure if this will
>     -- be the wrong thing elsewhere.
>     toLoc (A.Label s) = "$" ++ s

> instance ToLocation Ref where
>     toLoc (Ref (O s)) = toLoc (O s)
>     toLoc (Ref r) = "(" ++ toLoc r ++ ")"

> instance ToLocation Int where
>     toLoc i = "$" ++ toVal i

> instance ToValue Int where
>     toVal i = "0x" ++ showHex i ""

> instance ToValue A.Label where
>     toVal (A.Label s) = s

> instance ToValue String where
>     toVal s = s

> instance ToTarget A.Label where
>     toTarget (A.Label s) = s

> instance ToTarget String where
>     toTarget s = s

> instance ToTarget Loc where
>     toTarget (O 0) = "*(%ebp)"
>     toTarget (O s) = "*" ++ show (negate $ word s) ++ "(%ebp)"
>     toTarget (L l) = l
>     toTarget (R reg) = "*(%" ++ reg ++ ")"
>     toTarget (G l) = l
