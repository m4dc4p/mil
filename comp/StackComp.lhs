-----------------------------------------------------------------------
-- A compiler translating programs/expressions in MatchLang
-- into code for a stack-based abstract machine.
--
-- Load using:  hugs -98 MatchComp.hs
--
-- Mark P Jones, March 2009

> module StackComp where

> import Control.Monad(foldM)
> import Control.Monad.State
> import Control.Monad.Writer

> import MatchLang

-- Target language: ---------------------------------------------------

> data Block = Block Lab [Instr] End -- A basic block

> data Instr = Push Loc          -- Push contents of location onto stack
>            | Enter             -- Enter closure on top of stack, arg below
>            | Alloc String Int  -- Allocate object with n var slots
>            | Store Int         -- Store top into field below
>            | Reset Int         -- Reset stack
>            | SlideTo Int       -- Slide top element down stack to pos n
>              deriving Show

> data End   = Test CFun Loc Lab (Maybe Lab)
>            | Goto Lab
>            | Return
>            | Halt
>              deriving Show

> data Loc   = Stack Int      -- argument to this function (on the stack)
>            | Field Loc Int  -- value stored in closure for this function
>            | Const Int      -- a constant value
>            | Undef Var      -- undefined variable
>              deriving Show
         
> arg, clo  :: Loc
> arg        = Stack 0        -- location of the argument
> clo        = Stack 1        -- location of the closure pointer

> type Lab   = String         -- label

-- Environments: ------------------------------------------------------

> type Env   = [(Var, Loc)]

> app       :: Env -> Var -> Loc  -- lookup, should not fail
> app rho v  = head ([ l | (w,l) <- rho, w==v ] ++ [Undef v])

-- A Monad for Compilation: -------------------------------------------

> type Codegen = StateT (Int, Lab, [Instr]) (Writer [Block])

> codeGen     :: Expr -> [Block]
> codeGen e    = snd
>              $ runWriter
>              $ execStateT (do compExpr e [] 0; mkBlock Halt)
>              $ (0, "main", [])

> newBlock    :: Codegen () -> End -> Codegen Lab
> newBlock c e = do (n, l, is) <- get
>                   let b = mkLab n
>                   put (1+n, b, [])
>                   c
>                   n' <- mkBlock e
>                   put (n', l, is)
>                   return b

> labelEnd    :: (Lab -> End) -> (Lab -> Codegen ()) -> Codegen ()
> labelEnd e f = do (n, l, is) <- get
>                   let b = mkLab n
>                   put (1+n, l, is)
>                   f b
>                   n' <- mkBlock (e b)
>                   put (n', b, [])

> mkLab       :: Int -> Lab
> mkLab n      = "l" ++ show n

> mkBlock     :: End -> Codegen Int
> mkBlock e    = do (n, l, is) <- get
>                   tell [Block l (reverse is) e]
>                   return n

> emit        :: Instr -> Codegen ()
> emit i       = do (n, l, is) <- get
>                   put (n, l, i:is)

-- Compilation Rules: -------------------------------------------------

The code that is produced by compiling an expression will result in
pushing a single value onto the top of the stack.  The parameters to
the compExpr function specify:
 - the expression to compile;
 - an environment mapping variables to locations; and
 - an integer specifying the number of arguments on the stack when
   evalution of the expression begins.

> compExpr     :: Expr -> Env -> Int -> Codegen ()

> compExpr (EVar v) env n
>               = emit (Push (app env v))

> compExpr (ELit v) env n
>               = emit (Push (Const v))

> compExpr (ECon t es) env n
>               = do emit (Alloc t (length es))
>                    forM_ (zip es [1..]) $ \(e, i) ->
>                      do compExpr e env (n+1)
>                         emit (Store i)

> compExpr (EApp e1 e2) env n
>               = do compExpr e2 env n
>                    compExpr e1 env (n+1)
>                    emit Enter

> compExpr (ELet v e e') env n
>               = do compExpr e env n
>                    compExpr e' ((v, Stack n):env) (n+1)
>                    emit (SlideTo n)

> compExpr (EMat m) env n
>   | p == 0    = do compMatch m env n Abort []; emit (SlideTo n)
>   | otherwise = do bl <- newBlock (compMatch m env 2 Abort args) Return
>                    cl <- foldM copyClosure bl (reverse clovars)
>                    fvClosure cl (map (app env) fvs)
>     where p       = numParams m
>           fvs     = freeMatch m
>           nfvs    = length fvs
>           clovars = take (p-1) [1+nfvs..]
>           args    = map (Field clo) clovars ++ [arg]

Calculate the number of parameters in a Match:

> numParams             :: Match -> Int
> numParams (MPat _ m)   = 1 + numParams m
> numParams (MGrd _ m)   = numParams m
> numParams (MAlt m1 m2) = max (numParams m1) (numParams m2)
> numParams (MExp e)     = 0

Create a closure with label l and n free variables by copying (n-1)
values from the current closure and then adding the current argument:

> copyClosure    :: Lab -> Int -> Codegen Lab
> copyClosure l n = newBlock
>                    (do emit (Alloc l n)
>                        forM_ [1..n-1] $ \i ->
>                          do emit (Push (Field clo i))
>                             emit (Store i)
>                        emit (Push arg)
>                        emit (Store n))
>                    Return

Create a closure with a given label and containing the values from the
given list of locations:

> fvClosure     :: Lab -> [Loc] -> Codegen ()
> fvClosure l vs = do emit (Alloc l (length vs))
>                     forM_ (zip vs [1..]) $ \ (v, i) ->
>                       do emit (Push v)
>                          emit (Store i)

-- Compiling Matches: -------------------------------------------------

The following datatype provides a way to describe what should happen
when a Match fails:

> data OnFail = Abort | FailTo Lab Int Lab

Specifically, "Abort" indicates a failed Match that will result in a
full program abort, while "FailTo l n l'" indicates that we should
branch to label l' if the current stack has precisely n elements and
to label l otherwise.  (The code at label l will perform a Reset n
before continuing on to l'.)

> handleFail        :: Int -> OnFail -> Maybe Lab
> handleFail m Abort = Nothing
> handleFail m (FailTo l2 n l3)
>                    = Just (if m>n then l2 else l3)

The code that is produced by compiling a match pushes a single result
onto the stack, just like an expression, but we require two additional
parameters to specify:
 - what the program should do when a match fails;
 - the list of locations where arguments for MPats can be found.

> compMatch :: Match -> Env -> Int -> OnFail -> [Loc] -> Codegen ()

> compMatch (MExp e) env n f as
>   = compExpr e env n

> compMatch (MAlt m1 m2) env n f as
>   = labelEnd Goto (\l1 ->
>       do l3 <- newBlock (compMatch m2 env n f as) (Goto l1)
>          l2 <- newBlock (emit (Reset n))          (Goto l3)
>          compMatch m1 env n (FailTo l2 n l3) as)

> compMatch (MGrd g m) env n f as
>   = do (env', n') <- compGuard g env n f
>        compMatch m env' n' f as

> compMatch (MPat p m) env n f (a:as)
>   = do (env', n') <- compPat p env n a f
>        compMatch m env' n' f as

-- Compiling Patterns: ------------------------------------------------

A pattern is compiled to code that checks that a value in a specified
location matches a given pattern.  A pattern can also bind variables,
pushing new values on to the stack and adding new bindings to the
environment.  The parameters for compPat specify:
 - the pattern to compile;
 - the initial environment;
 - the initial number of arguments on the stack;
 - the location of the value that we are matching; and
 - the behavior that is required if the match fails.
The return results specify:
 - the environment after a successful match; and
 - the number of values on the stack after a successful match.

> compPat :: Pat -> Env -> Int -> Loc -> OnFail -> Codegen (Env, Int)

> compPat (PCon c ps) env n l f
>   = do labelEnd (\l1 -> Test c l l1 (handleFail n f)) (\l1 -> return ())
>        foldM (\(env, n) (p, i) ->
>                 do emit (Push (Field l i))
>                    compPat p env (n+1) (Stack n) f)
>              (env, n)
>              (zip ps [1..])

> compPat (PVar v) env n l f
>   = return ((v, l):env, n)

> compPat (PGrd p g) env n l f
>   = do (env', n') <- compPat p env n l f
>        compGuard g env' n' f

-- Compiling Guards: --------------------------------------------------

Guards are compiled to code that checks the guard and/or binds some
variables.  The parameters and return results for compGuard are the
same as those for compPat except that there is no location parameter
for a value to be matched.

> compGuard :: Guard -> Env -> Int -> OnFail -> Codegen (Env, Int)

> compGuard (GLet v e) env n f
>   = do compExpr e env n
>        return ((v, Stack n):env, n+1)

> compGuard (GGet p e) env n f
>   = do compExpr e env n
>        compPat p env (n+1) (Stack n) f

-----------------------------------------------------------------------
