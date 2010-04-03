-----------------------------------------------------------------------
-- A compiler translating programs/expressions in MatchLang
-- into code for a register-based abstract machine.
--
-- The code that is generated here is missing a few important
-- details.  In particular, some extra structure is needed to
-- partition the generated blocks and temporaries across the
-- set of "procedures".
--
-- Load using:  hugs -98 RegComp.hs
--
-- Mark P Jones, March 2009

> module RegComp where

> import Control.Monad(foldM)
> import Control.Monad.State
> import Control.Monad.Writer

> import MatchLang

-- Target language: ---------------------------------------------------

> data Block = Block Lab [Instr] End -- A basic block

> data Instr = Alloc Temp String Int -- Allocate object with tag & length
>            | Store Temp Int Temp   -- Store a value in an object
>            | Load  Temp Temp Int   -- Load a value from an object
>            | Enter Temp Temp Temp  -- enter closure with an argument
>            | Copy  Temp Temp       -- copy between temporaries
>            | Set Temp Int               -- Set a register to a certain value.

> instance Show Instr where
>   show (Alloc t c i) = t ++ " <- alloc " ++ c ++ " " ++ show i
>   show (Store t i x) = t ++ "[" ++ show i ++ "] <- " ++ x
>   show (Load  t x i) = t ++ " <- " ++ x ++ "[" ++ show i ++ "]"
>   show (Enter t f x) = t ++ " <- " ++ f ++ " @ " ++ x
>   show (Copy  t s)   = t ++ " <- " ++ s
>   show (Set t i)   = t ++ " := " ++ show i

> data End   = Test CFun Temp Lab OnFail
>            | Goto Lab
>            | Return Temp
>            | Halt

> instance Show End where
>   show (Test c t l1 l2) = "test " ++ t ++ " " ++ c ++ "? "
>                                   ++ l1 ++ " : " ++ show l2
>   show (Goto l)         = "goto " ++ l
>   show (Return t)       = "ret " ++ t
>   show Halt             = "halt"

> type Temp  = String

> arg, clo  :: Temp
> arg        = "arg"          -- the "argument register"
> clo        = "clo"          -- the "closure register"

> type Lab   = String         -- label

-- Environments: ------------------------------------------------------

> type Env   = [(Var, Temp)]

> app       :: Env -> Var -> Temp  -- lookup, should not fail
> app env v  = head ([ t | (w, t) <- env, w==v ] ++ ["undef:" ++ v])

-- A Monad for Compilation: -------------------------------------------

> type Codegen = StateT (Int, Lab, [Instr]) (Writer [Block])

> codeGen     :: Expr -> [Block]
> codeGen e    = snd
>              $ runWriter
>              $ execStateT (do compExpr e []; mkBlock Halt)
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

> newTemp     :: Codegen Temp
> newTemp      = do (n, l, is) <- get
>                   put (n+1, l, is)
>                   return ("t" ++ show n)

> mkBlock     :: End -> Codegen Int
> mkBlock e    = do (n, l, is) <- get
>                   tell [Block l (reverse is) e]
>                   return n

> emit        :: Instr -> Codegen ()
> emit i       = do (n, l, is) <- get
>                   put (n, l, i:is)

-- Compilation Rules: -------------------------------------------------

The code that is produced by compiling an expression will leave the
result in a tempory variable (a new temporary will be allocated if
necessary).  The parameters to the compExpr function specify:
 - the expression to compile; and
 - an environment mapping variables to locations.
The return result is the temporary in which the result may be found.

> compExpr     :: Expr -> Env -> Codegen Temp

> compExpr (EVar v) env
>               = return (app env v)

> compExpr (ELit v) env
>               = do t <- newTemp
>                    emit (Set t v)
>                    return t

> compExpr (ECon c es) env
>               = do t <- newTemp
>                    emit (Alloc t c (length es))
>                    forM_ (zip es [1..]) $ \(e, i) ->
>                      do x <- compExpr e env
>                         emit (Store t i x)
>                    return t

> compExpr (EApp e1 e2) env
>               = do x <- compExpr e2 env
>                    f <- compExpr e1 env
>                    t <- newTemp
>                    emit (Enter t f x)
>                    return t

> compExpr (ELet v e e') env
>               = do t <- compExpr e env
>                    compExpr e' ((v, t):env)

Having trouble understanding this code.

> compExpr (EMat m) env
>   = do t <- newTemp -- allocate a new register for result
>        if p==0
>          -- If match has no parameters, compile it without
>          -- consuming any "arguments".
>          then do compMatch m env t Abort []
>                  return t
>          -- Otherwise, construct a series of closures
>          -- which will consume all necessary arguments and put
>          -- them in a final closure.
>          else do bl <- newBlock
>                         (do -- Copy arguments from closure to new
>                             -- registers.
>                             args <- forM (reverse clovars) (\i ->
>                                       do a <- newTemp
>                                          emit (Load a clo i)
>                                          return a)
>                             -- Copy closure values into free variable
>                             -- registers. Necessary if environment
>                             -- does not update?
>                             forM_ (zip fvs [1..]) (\(v, i) ->
>                               emit (Load v clo i))
>                             -- Compile match with args from closure in
>                             -- registers. 
>                             compMatch m env t Abort (reverse args++[arg]))
>                         -- Final result returned.
>                         (Return t)
>                  -- Construct series of closures which consume all
>                  -- match parameters.
>                  cl <- foldM copyClosure bl (reverse clovars)
>                  -- Create initial closure with free variables only,
>                  -- which jumps to first closure created with
>                  -- foldM above.
>                  fvClosure cl (map (app env) fvs)
>     where p       = numParams m
>           fvs     = freeMatch m
>           nfvs    = length fvs
>           clovars = take (p-1) [1+nfvs..]

Note that we load arguments from the closure in reverse order; this
will make it possible to jump in to the code of the closure with some
(or all) arguments already loaded.

Calculate the number of parameters in a Match:

> numParams             :: Match -> Int
> numParams (MPat _ m)   = 1 + numParams m
> numParams (MGrd _ m)   = numParams m
> numParams (MAlt m1 m2) = max (numParams m1) (numParams m2)
> numParams (MExp e)     = 0

Create a closure with label l and n free variables by copying (n-1)
values from the current closure and then adding the current argument:

> copyClosure    :: Lab -> Int -> Codegen Lab
> copyClosure l n = do c <- newTemp
>                      newBlock
>                       (do emit (Alloc c l n)
>                           forM_ [1..n-1] $ \i ->
>                             do t <- newTemp
>                                emit (Load t clo i)
>                                emit (Store c i t)
>                           emit (Store c n arg))
>                       (Return c)

This code should probably be rewritten (a) to load vars from the
incoming closure in reverse order; and (b) to load all vars from
the incoming closure before writing them back to the result (LCM
will help reduce register pressure later on).  This will allow us
to jump into the copyClosure body part way through.  Note that we
would also have to position the Alloc instruction after all of the
intial loads to make this work properly.

Create a closure with a given label and containing the values from the
given list of locations:

> fvClosure     :: Lab -> [Temp] -> Codegen Temp
> fvClosure l ts = do c <- newTemp
>                     emit (Alloc c l (length ts))
>                     forM_ (zip ts [1..]) $ \ (t, i) ->
>                       emit (Store c i t)
>                     return c

-- Compiling Matches: -------------------------------------------------


The following datatype provides a way to describe what should happen
when a Match fails:

> data OnFail = Abort | FailTo Lab

> instance Show OnFail where
>   show Abort      = "abort"
>   show (FailTo l) = l

Specifically, "Abort" indicates a failed Match that will result in a
full program abort, while "FailTo l" indicates that we should branch
to label l.

The code that is produced by compiling a match pushes will leave a
result in a temporary variable.  Unlike the code for compExpr, we
take an extra parameter here to specify which temporary should be
used for the result.  This makes it easier to arrange for a single
temporary to be used, even if there are multiple alternatives in
the match.  On the other hand, it also requires the introduction of
copy instructions.  With luck, we'll be able to eliminate many of
those copy instructions later via copy propagation and dead code
elimination.

The arguments to compMatch specify:
 - the match to be compiled;
 - the initial environment;
 - the temporary that is to be used for the result;
 - the behavior that is required when a match fails;
 - the list of temporaries where arguments for MPats can be found.

> compMatch :: Match -> Env -> Temp -> OnFail -> [Temp] -> Codegen ()

> compMatch (MExp e) env t f as
>   = do t' <- compExpr e env
>        emit (Copy t t')

> compMatch (MAlt m1 m2) env t f as
>   = labelEnd Goto (\l1 ->
>       do l2 <- newBlock (compMatch m2 env t f as) (Goto l1)
>          compMatch m1 env t (FailTo l2) as)

> compMatch (MGrd g m) env t f as
>   = do env' <- compGuard g env f
>        compMatch m env' t f as

> compMatch (MPat p m) env t f (a:as)
>   = do env' <- compPat p env a f
>        compMatch m env' t f as

-- Compiling Patterns: ------------------------------------------------

A pattern is compiled to code that checks that a value in a specified
temporary matches a given pattern.  A pattern can also bind variables
(in new temporaries) with corresponding new entries in the environment.
The parameters for compPat specify:
 - the pattern to compile;
 - the initial environment;
 - the temporary containing the value that we are matching; and
 - the behavior that is required if the match fails.
The return result specifies the environment after a successful match.

> compPat :: Pat -> Env -> Temp -> OnFail -> Codegen Env

> compPat (PCon c ps) env t f
>   = do labelEnd (\l1 -> Test c t l1 f) (\l1 -> return ())
>        foldM (\env (p, i) ->
>                 do x <- newTemp
>                    emit (Load x t i)
>                    compPat p env x f)
>              env
>              (zip ps [1..])

[Aside: Note that we may want to break the use of Test into two
parts; a load that fetches the tag of an object, followed by the
actual test.  This would allow optimization to detect (and perhaps
eliminate) multiple loads of an object's tag.]

> compPat (PVar v) env t f
>   = return ((v, t):env)

> compPat (PGrd p g) env t f
>   = do env' <- compPat p env t f
>        compGuard g env' f

-- Compiling Guards: --------------------------------------------------

Guards are compiled to code that checks the guard and/or binds some
variables.  The parameters and return results for compGuard are the
same as those for compPat except that there is no temporary parameter
for a value to be matched.

> compGuard :: Guard -> Env -> OnFail -> Codegen Env

> compGuard (GLet v e) env f
>   = do t <- compExpr e env
>        return ((v, t):env)

> compGuard (GGet p e) env f
>   = do t <- compExpr e env
>        compPat p env t f

-----------------------------------------------------------------------
