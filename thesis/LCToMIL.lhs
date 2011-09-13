> {-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
>   , NamedFieldPuns, TypeFamilies, ScopedTypeVariables
>   , FlexibleInstances #-}

> module LCToMIL

> where

> import Control.Monad.State (State, execState, modify, gets, get, put)
> import Control.Monad (when)
> import Text.PrettyPrint 
> import Data.List (sort, nub, delete, (\\))
> import Data.Maybe (fromMaybe, isJust, isNothing, catMaybes, fromJust)
> import Data.Map (Map, (!))
> import qualified Data.Map as Map
> import Data.Set (Set)
> import qualified Data.Set as Set
> import Compiler.Hoopl

> import MIL
> import Syntax.LambdaCase hiding (Alt)
> import qualified Syntax.LambdaCase as LC
> import Util

This module implements a compiler from LC programs to MIL programs. 

The compilStmtM function implements the majority of the translation
from LC to MIL:

> compileStmtM :: Expr 
>   -> (TailM -> CompM (ProgM O C))
>   -> CompM (ProgM O C)

The first argument represents the LC expression to translate. The
result uses our compiler monad to create a MIL basic block. I call the
second argument the "compilation context". The context represents
everything translated so far, except for a hole where our current
expression's translation should go. Therefore, compileStmtM translates
its first argument into a TailM value and passes it the context. 

Notice the context itself produces a basic block. In some cases, the
context's result is retured by compileStmtM directly. In other cases,
it is used to produce out-of-line blocks that are managed by the
compiler monad and not returned directly. '

The CompM monad in which compileStmtM executes carries a flag that
represents if the current LC expression should be evaluated as a
side-effecting compuation or as a pure expression. compileStmtM must
produce different code to deal with LC monadic "computations" versus
pure expresssions. The differences will be highlighted I describe the
relevant portions of compileStmtM.

We first look at the EPrim term. This LC term evaluates a
primitive function, presumably implemented in the runtime system. 

> compileStmtM (EPrim p _) ctx = do 

We use the getDestOfName utility function to find the label associated
with the primitive. If the label doesn't exist, we exit with an error.

>   dest <- getDestOfName p
>   when (isNothing dest) (error $ "Could not find primitive '" ++ p ++ "' in predefined.")

Otherwise, we construct a Goto value with the destination found and
pass it to our context.  Note that we don't worry about the location
of the result of evaluating the primitive -- the context already knows
where the result will go.

>   ctx (Goto (fromJust dest) [])

The ECon term creates a data value. We implement ECon using a
series of pre-generated primitives, one for each constructor of each
known data type. Really, ECon compiles to almost the same MIL code as
EPrim.

> compileStmtM (ECon cons _) ctx = do 
>   dest <- getDestOfName ("mkData_" ++ cons)
>   when (isNothing dest) (error $ "Could not find '" ++ "mkData_" ++ cons ++ "' in predefined.")
>   ctx (Goto (fromJust dest) [])

The ELam term defines an anonymous function, and when evaulated it
creates a value representing the function. Compiling this term
requires that we accomplish two tasks: create a new function
definition, and generate code to create the value representing the function.

> compileStmtM body@(ELam v _ b) ctx = do

To create a new function definition, we essentially create a new
"compilation context." The call to cloDefn generates a new MIL basic
block that holds the translated body of the lambda. cloDefn also generates code
which can retrieve the lambda body's free variables. cloDefn
returns a name and label which can be used to call the new function.

>   free <- getFree body
>   (name, label) <- do
>     name <- newTop "absBody"
>     cloDefn name v free b 
>   setDest name label

Now that we know where to find the translated body of the lambda term,
we can generate code to create a closure value representing the lambda
term. We pass this closure to our context.

>   ctx (Closure (name, label) free)

> compileStmtM (ECase e lcAlts) ctx = do
>   let alts = map toAlt lcAlts
>   r <- fresh "result"
>   f <- ctx (Return r) >>= \rest -> callDefn "caseJoin" (\n l -> return rest)
>   let compAlt (Alt cons vs body) = do
>         body' <- callDefn ("altBody" ++ cons) (\n l -> compileStmtM body (mkBind n l r f))
>         return (Alt cons vs body')
>   altsM <- mapM compAlt alts
>   compVarM e $ \v -> return (mkLast (CaseM v altsM))
>   where
>     callDefn :: String -> (Name -> Label -> CompM (ProgM O C)) -> CompM TailM
>     callDefn n body = do 
>       (name, label) <- newTop n >>= \f -> blockDefn f [] body
>       setDest name label
>       return (Goto (name, label) [])

> compileStmtM (EApp e1 e2) ctx 
>   = compVarM e1 $ \f ->
>     compVarM e2 $ \g ->
>       ctx (Enter f g)

> compileStmtM (EBind v _ b r) ctx = do
>   rest <- compileStmtM r ctx
>   asMonadic (compileStmtM b $ \t -> do
>     return (mkMiddle (v `Bind` t) <*> rest))

> compileStmtM (ELet (Decls defs) outerBody) ctx = compVars (getDefns defs)
>   where
>     compVars [Defn name _ letBody] = 
>       compVarM letBody $ \v -> do
>         rest <- compileStmtM outerBody ctx
>         return (mkMiddle (Bind name (Return v)) <*> rest)
>     compVars (Defn name _ letBody : ds) = do
>       rest <- compVars ds 
>       compVarM letBody $ \v -> do
>         return (mkMiddle (Bind name (Return v)) <*> rest)

> compileStmtM (EVar v _) ctx 
>   = ctx (Return v) `unlessMonad` ctx (Run v)

> compileStmtM (ENat n) ctx
>   = ctx (LitM n)

> compileStmtM (EFatbar _ _) _ 
>   = error "EFatbar not implemented."

> compileStmtM (EBits _ _) _ 
>   = error "EBits not implemented."

> -- | Compiler state. 
> data CompS = C { compI :: Int -- ^ counter for fresh variables
>                , compG :: ProgM C C -- ^ Program control-flow graph.
>                , compT :: Map Name (Maybe Dest) -- ^ top-level function names and their location.
>                , compM :: (Bool, [Bool]) } -- ^ Allows nested
>                                              -- monadic
>                                              -- computation. "Top"
>                                              -- value indicates if we
>                                              -- are compiling
>                                              -- monadically or
>                                              -- not. List serves as a
>                                              -- stack of previous
>                                              -- states. Starts non-monadic (False, []).

> -- | Create the initial state for our compiler.
> mkCompS i userTops predefined = 
>   let mkMap = map ((\dest@(n, _) -> (n, Just dest)) . destOfEntry . snd) . entryPoints 
>       tops = zip userTops (repeat Nothing)
>   in C i emptyClosedGraph (Map.fromList (tops ++ mkMap predefined)) (False, [])
               
> type CompM = State CompS
> type Free = [Name]

> type Def = (Name, Expr)

> emptyPrelude :: ([Name], ProgM C C)
> emptyPrelude = ([], emptyClosedGraph)

> -- | Pre-compiled primitive functions
> -- supporting monadic actions.
> prelude :: ([Name], ProgM C C)
> prelude = 
>   let comp (name, impl) = do
>         impl' <- impl
>         (names, g, i) <- get
>         modify (\(names, g, i) -> (name : names,  impl' |*><*| g, i))
>         return ()
>       (names, preludeProg, _) = foldr (\prim -> execState (comp prim)) ([], emptyClosedGraph, 0 :: Int) prims
>   in (names, preludeProg)

> compile :: [Name] -> ([Name], ProgM C C) -> [Def] -> ProgM C C
> compile userTops (primNames, predefined) defs = 
>     foldr (|*><*|) predefined . snd . foldr compileDef (200, []) $ defs
>   where
>     -- Compiles a single LC definition and returns the compiler
>     -- state, to be used during the next definition.
>     compileDef :: Def -> (Int, [ProgM C C]) -> (Int, [ProgM C C])
>     compileDef p (i, ps) = 
>       let result = execState (newDefn p) (mkCompS i userTops predefined)
>       in (compI result + 1, compG result : ps)

> -- Creates a new function definition
> -- using the arguments given and adds it
> -- to the control flow graph.    
> newDefn :: (Name, Expr) -> CompM ()
> newDefn (name, body@(ELam v _ b)) = do
>   free <- getFree body
>   cloDefn name v free b 
>   return ()


> compVarM :: Expr 
>   -> (Name -> CompM (ProgM O C))
>   -> CompM (ProgM O C)
> compVarM (EVar v _) ctx = ctx v
> compVarM e ctx = compileStmtM e $ \t -> do
>   v <- fresh "v"
>   rest <- ctx v
>   return (mkMiddle (v `Bind` t) <*> rest)

> mkBind :: Name -> Label -> Name -> TailM -> TailM -> CompM (ProgM O C)
> mkBind n l r f t = return (mkMiddle (Bind r t) <*> mkLast (Done n l f))

> free :: Expr -> Free
> free = nub . free'
>   where
>     free' (EVar v _) = [v]
>     free' (EPrim v _) = []
>     free' (ENat _) = []
>     free' (EBits _ _) = []
>     free' (ECon _ _) = []
>     free' (ELam v _ expr) = v `delete` nub (free' expr)
>     free' (ELet (Decls decls) expr) = free' expr \\ (map (\(Defn n _ _) -> n) $ getDefns decls)
>     free' (ECase expr alts) = nub (free' expr ++ concatMap (\(LC.Alt _ _ vs e) -> nub (free' e) \\ vs) alts)
>     free' (EApp e1 e2) = nub (free' e1 ++ free' e2)
>     free' (EFatbar e1 e2) = nub (free' e1 ++ free' e2)
>     free' (EBind v _ e1 e2) = nub (free' e1 ++ v `delete` nub (free' e2))

      
> -- | Create a fresh variable with the given
> -- prefix.
> fresh :: String -> CompM String
> fresh prefix = do
>   i <- gets compI
>   modify (\s@(C { compI }) -> s { compI = compI + 1})
>   return (prefix ++ show i)

> -- | Create a new unique value; used in the
> -- instance declaration for (UniqueMonad CompM).
> freshVal :: CompM Unique
> freshVal = do
>   i <- gets compI
>   modify (\s@(C { compI }) -> s { compI = compI + 1})
>   return (intToUnique i)

> -- | Make a new top-level function name, based on the
> -- prefix given.
> newTop :: Name -> CompM Name
> newTop name = do
>     f <- fresh name
>     modify (\s@(C { compT }) -> s { compT = Map.insert f Nothing compT })
>     return f

> -- | Gets free variables in the lambda, accounting
> -- for the current list of top-level names. e should
> -- be a lambda
> getFree :: Expr -> CompM [Name]
> getFree lam@(ELam _ _ _) = do
>   tops <- gets compT >>= return . Map.keys
>   return (free lam \\ tops)
> getFree _ = error "getFree called on non-lambda expression."

> setDest :: Name -> Label -> CompM ()
> setDest name label = 
>   modify (\s@(C { compT }) -> s { compT = Map.insert name (Just (name, label)) compT })

> getDestOfName :: Name -> CompM (Maybe Dest)
> getDestOfName name = gets compT >>= return . fromMaybe Nothing . Map.lookup name

> -- | Add a new block.
> blockDefn :: Name -> [Name] -> (Name -> Label -> CompM (ProgM O C)) -> CompM Dest
> blockDefn name args progM = withNewLabel $ \l -> do
>   rest <- progM name l
>   addProg (mkFirst (BlockEntry name l args) <*> rest)
>   return (name, l)
  
> -- | Compile a lambda expression. Name, arg, and fvs
> -- all refer to the enclosing lambda. body is the *body*
> -- of the lambda.
> cloDefn :: Name -> Name -> [Name] -> Expr -> CompM Dest
> cloDefn name arg fvs body@(ELam v _ b) = withNewLabel $ \l -> do
>   let args = fvs ++ [arg]
>   dest <- cloDefn ("absBody" ++ name) v args b
>   addProg (mkFirst (CloEntry name l fvs arg) <*>
>            mkLast (Done name l (Closure dest args)))
>   return (name, l)

> cloDefn name arg fvs body@(EBind _ _ _ _) = withNewLabel $ \l -> do
>   let args = fvs ++ [arg]
>   dest <- blockDefn ("block" ++ name) args (\n l -> compileStmtM body (return . mkLast . Done n l))
>   addProg (mkFirst (CloEntry name l fvs arg) <*>
>            mkLast (Done name l (Thunk dest args)))
>   return (name, l)

> cloDefn name arg fvs body = withNewLabel $ \l -> do
>   let args = fvs ++ [arg]
>   dest <- blockDefn ("block" ++ name) args (\n l -> compileStmtM body (return . mkLast . Done n l))
>   addProg (mkFirst (CloEntry name l fvs arg) <*>
>            mkLast (Done name l (Goto dest args)))
>   return (name, l)

> -- | Add a program (C C block) to the list of blocks
> -- maintained by the monad.
> addProg :: ProgM C C -> CompM ()
> addProg block = modify (\s@(C { compG }) -> s { compG = block |*><*| compG })

> -- | Do something with a new label.
> withNewLabel :: UniqueMonad m => (Label -> m a) -> m a
> withNewLabel f = freshLabel >>= f
  
> -- | Run the compiler in monadic
> -- mode. Restore the previous mode when finished.
> asMonadic :: CompM a -> CompM a
> asMonadic m = do
>   modify (\s@(C _ _ _ (flag, stack)) -> s { compM = (True, flag : stack) })
>   a <- m
>   modify (\s@(C _ _ _ (_, (flag:stack))) -> s { compM = (flag,stack) })
>   return a
  
> -- | Run the left (pure) compilation, unless we
> -- are compiling monadically. Run the right
> -- in that case.
> unlessMonad :: CompM (ProgM O C)
>         -> CompM (ProgM O C)
>         -> CompM (ProgM O C)
> unlessMonad pure monad = inMonad >>= \b -> if b then monad else pure
>   where
>     -- | Are we in monadic compilation mode?
>     inMonad :: CompM Bool
>     inMonad = let f (C { compM }) = fst compM
>               in gets f

> toAlt :: LC.Alt -> Alt Expr
> toAlt (LC.Alt cons _ vs expr) = Alt cons vs expr

> getDefns :: [Decl] -> [Defn]
> getDefns = concatMap f
>   where
>     f (Mutual decls) = error "Unable to compile mutually recursive Let declarations."
>     f (Nonrec decl) = [decl]

> -- Required so we can generate
> -- unique Hoopl labels when 
> instance UniqueMonad CompM where
>   freshUnique = freshVal

> -- Required so we can generate unique hoopl labels 
> -- when creating our prelude from primitive definitions.
> instance UniqueMonad (State ([Name], ProgM C C, Int)) where
>   freshUnique = do
>     (_, _, i) <- get
>     modify (\(n, g, j) -> (n, g, j + 1))
>     return (intToUnique i)

