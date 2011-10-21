> {-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes, NamedFieldPuns, TypeFamilies, ScopedTypeVariables, FlexibleInstances #-}
> module LCToMIL (compile, Def, prelude, fromProgram)

> where

> import Control.Monad.State (State, execState, modify, gets, get, put)
> import Control.Monad (when)
> import Text.PrettyPrint 
> import Data.List (sort, nub, delete, (\\), isInfixOf)
> import Data.Maybe (fromMaybe, isJust, isNothing, catMaybes, fromJust)
> import Data.Map (Map, (!))
> import qualified Data.Map as Map
> import Data.Set (Set)
> import qualified Data.Set as Set
> import Compiler.Hoopl
> import Debug.Trace

> import MIL
> import Syntax.Common
> import Syntax.LambdaCase hiding (Alt)
> import qualified Syntax.LambdaCase as LC
> import Util

This module implements a compiler from LC programs to MIL programs. 

The compilStmtM function implements the majority of the translation
from LC to MIL:

> compileStmt :: Expr 
>   -> (TailM -> CompM (ProgM O C))
>   -> CompM (ProgM O C)

The first argument represents the LC expression to translate. The
result uses our compiler monad to create a MIL basic block. I call the
second argument the "compilation context". The context represents
everything translated so far, except for a hole where our current
expression's translation should go. Therefore, compileStmt translates
its first argument into a TailM value and passes it the context. 

Notice the context itself produces a basic block. In some cases, the
context's result is retured by compileStmt directly. In other cases,
it is used to produce out-of-line blocks that are managed by the
compiler monad and not returned directly. 

I will describe the translation of each LC expression into MIL
instructions, starting with ECon. The ECon term creates a data
value. 

> compileStmt (ECon (Ident cons _) _) ctx = do 

We implement ECon using a series of pre-generated primitives, one for
each constructor of each known data type. Therefore, we first look for
the primitive with a special, pre-determined name. |getDestOfName| looks
up the name of a MIL block and returns a |Maybe Dest| value, indicating
if the name exists in the current program.

>   dest <- getDestOfName ("mkData_" ++ cons)
>   when (isNothing dest) (error $ "Could not find '" ++ "mkData_" ++ cons ++ "' in predefined.")

Assuming the name exists, compileStmt puts |Goto| instruction to
execute the body of the primitive. Notice no arguments are given
to |Goto|. If the constructor takes arguments, the block referred
to here will return a closure and normal function application
will take care of gatehring arguments up and eventually executing
the data constructor primitive.

>   ctx (Goto (fromJust dest) [])

The ELam term defines an anonymous function, and when evaulated it
creates a value representing the function. Compiling this term
requires that we accomplish two tasks: create a new function
definition, and generate code to create the closure representing the
function.

> compileStmt body@(ELam (Ident v _) _ b) ctx = withFree (const (setFree body)) $ \free -> do
>   (name, label) <- do
>     name <- newTop "absBody"
>     withNewLabel $ \l -> do
>       rest <- case b of
>                 (ELam _ _ _) -> compileStmt b (return . mkLast . Done name l)
>                 _ -> do 
>                   bn <- newTop "absBlock"
>                   dest <- 
>                      blockDefn bn (free ++ [v]) 
>                        (\bn bl -> compileStmt b (return . mkLast . Done bn bl))
>                   return (mkLast (Done name l (Goto dest (free ++ [v]))))
>       addProg (mkFirst (CloEntry name l free v) <*> rest)
>       return (name, l)
>   setDest name label
>   ctx (Closure (name, label) free)

EBind evaluates its right-hand side as a monadic value. Therefore, the 
translated code for the monadic expression will evaluate to a monadic
thunk. 

> compileStmt bind@(EBind (Ident v _) _ _ _) ctx = withFree (return . delete v) $ \fvs -> do
>   name <- newTop "bindBody"
>   dest <- blockDefn name fvs $ \n l -> do
>     let compM (EBind (Ident v _) _ b r) = withFree (return . delete v) $ \_ -> do
>           rest <- compM r 
>           compResultVar b $ \n -> return (mkMiddle (v `Bind` (Run n)) <*> rest)
>         compM e = compResultVar e (\v -> return (mkLast (Done n l (Run v))))
>     compM bind 
>   ctx (Thunk dest fvs)

An EVar term, in this case, must appear in "variable" position or it 
would be handled by EApp, EBind, or other terms. Therefore, we apply
the Return instruction to variable in order to "wrap" the value and 
place it in context. 

> compileStmt (EVar (Ident v _) _) ctx = do
>   top <- isTopLevel v
>   if isJust top
>    then do
>      ctx (Goto (fromJust top) [])
>    else
>      ctx (Return v) 

The EApp term evaluates both its arguments using compResultVar, giving
names to the locations holding the values represented by the arguments
to EApp. 

> compileStmt (EApp e1 e2) ctx 
>   = compResultVar e1 $ \f ->
>     compResultVar e2 $ \g ->

Now, I apply the Enter instruction to the two variables produced by the
preceding. The first variable will always represent a closure or primitive
-- assuming the LC program given is type-correct, of course!

>       ctx (Enter f g)

> compileStmt _case@(ECase e lcAlts) ctx = do

The strategy for |ECase| evaluates the case expression and selects
an arm  in a separate block, created by the |compileCase|
function (explained below). 

>     caseEval <- compileCase 

The result of that block is the result of the case expression. I put
that result in a new variable and pass it to the context provided
initially. 

>     r <- fresh "result"
>     rest <- ctx (Return r)

The context returns the rest of the program. Now I bind the
value of the case expression to the fresh variable and put it in
front of the rest of the program, guaranteeing the variable will hold
a value before the rest of the program executes.

>     return (mkMiddle (r `Bind` caseEval) <*> rest)
>   where

|compileCase| creates a new block for our case expression, as well as
a block for each arm. The block for the case expression (|_case|)
needs access to all free variables; |free _case| calculates the free
variables in |_case|, and |withFree| makes them available to the code
that will compile the case expression.

>   compileCase = withFree (const (return $ free _case)) $ \fvs -> do

|compAlt| compiles creates a block for each arm and returns an |CompM Alt|
value representing the arm. The MIL |CaseM| instruction takes a list
of |Alt| values, each of which represents a block for a particular
case arm. We monadically compile each arm and collect the |CompM Alt| values
into a list.

>     altsM <- mapM compAlt (map toAlt lcAlts)

Now the block for evaluating the case expression is generated. The
block takes all free variables in the entire case expression
(including all arms).

>     caseName <- newTop "caseEval"
>     dest <- blockDefn caseName fvs 
>             (\_ _ -> 

The body of block evaluates the case expression and puts the result
in the variable represented by |v|. The block ends with the MIL |CaseM|
instruction, which will select the appropriate arm based on the value 
found in the variable represented by |v|.

>                compResultVar e $ \v -> return (mkLast (CaseM v altsM)))
>     return (Goto dest fvs)

|compAlt| creates a block for a case arm. The block only takes free variables
present in the current arm, so |compAlt| starts with a call to |setFree body|
so compiliation of the body sees the appropriate free variables.

>   compAlt (Alt cons vs body) = withFree (const (setFree body)) $ \afvs -> do
>     altName <- newTop (mkName "altBody" cons)                                  
>     altDest <- blockDefn altName afvs $ \n l -> do

The block for the arm evaulates the body of the arm and places it in
a new variable. The block ends by returning the value of that variable.

>       compResultVar body (return . mkLast . Done n l . Return)

Once a block for the arm has been created, I wrap it up in an |Alt| value
and return it.

>     return (Alt cons vs (Goto altDest afvs))

EPrim should only appear in "variable" position, by which I mean part
of a function application or on the right-hand side of an EBind
statement. The cases for EApp and EBind handle EPrim through the
compResultVar function. Therefore, we should not see an EPrim by itself, so
I report an error if the situation occurs.

> compileStmt (EPrim (Ident p _) _ _) ctx = do
>   dest <- getDestOfName p
>   when (isNothing dest) (error $ "primitive " ++ p ++ " not defined.")
>   ctx (Goto (fromJust dest) [])

> compileStmt (ELet (Decls defs) outerBody) ctx = compVars (getDefns defs)
>   where
>     compVars [Defn (Ident name _) _ letBody] = 
>       compBody name letBody $ \t -> do
>         rest <- compileStmt outerBody ctx
>         return (mkMiddle (Bind name t) <*> rest)
>     compVars (Defn (Ident name _) _ letBody : ds) = do
>       rest <- compVars ds 
>       compBody name letBody $ \t -> do
>         return (mkMiddle (Bind name t) <*> rest)
>     compBody name (Right body) ctx = withFree (const (return $ free body)) $ \lfvs -> do
>       -- Determine free variables
>       -- Create a block taking all free variables
>       -- as arguments, containing code representing
>       -- the body. 
>       -- Jump to the block and put the result in a varialbe
>       letName <- newTop (mkName "letBody" name)
>       letDest <- blockDefn letName lfvs (\ln ll ->
>                    compileStmt body (return . mkLast . Done ln ll))
>       ctx (Goto letDest lfvs)
>     compBody name (Left (prim, typs)) ctx = 
>       compileStmt (EPrim prim (error "evaluated type") (error "evaluated types")) ctx

> compileStmt (ENat n) ctx
>   = ctx (LitM n)

> compileStmt (EFatbar _ _) _ 
>   = error "EFatbar not implemented."

> compileStmt (EBits _ _) _ 
>   = error "EBits not implemented."

> compResultVar :: Expr 
>   -> (Name -> CompM (ProgM O C))
>   -> CompM (ProgM O C)
> compResultVar (EVar (Ident v _) _) ctx = do
>   top <- isTopLevel v
>   if isJust top
>    then do
>      v <- fresh "v"
>      rest <- ctx v
>      return (mkMiddle (v `Bind` (Goto (fromJust top) [])) <*> rest)
>    else
>      ctx v 
> compResultVar e ctx = compileStmt e $ \t -> do
>   v <- fresh "v"
>   rest <- ctx v
>   return (mkMiddle (v `Bind` t) <*> rest)

> -- | Add a new block.
> blockDefn :: Name -> [Name] -> (Name -> Label -> CompM (ProgM O C)) -> CompM Dest
> blockDefn name args progM = withNewLabel $ \l -> do
>   rest <- progM name l
>   addProg (mkFirst (BlockEntry name l args) <*> rest)
>   return (name, l)

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
>     foldr (|*><*|) predefined . snd . foldr compileDef (fst initialDefs, []) $ defs
>   where
>     -- Compiles a single LC definition and returns the compiler
>     -- state, to be used during the next definition.
>     compileDef :: Def -> (Int, [ProgM C C]) -> (Int, [ProgM C C])
>     compileDef p (i, ps) = 
>       let result = execState (newDefn p) (mkC i (snd initialDefs))
>       in (compI result + 1, compG result : ps)
>     -- Creates a new function definition
>     -- using the arguments given and adds it
>     -- to the control flow graph.    
>     newDefn :: (Name, Expr) -> CompM ()
>     newDefn (name, body) = do
>       _ <- setFree body
>       withFree return $ \args -> do
>         -- This ugliness makes sure we re-use the label
>         -- assigned to the top-level function. 
>         Just (_, label) <- gets compT >>= return . maybe Nothing id . Map.lookup name 
>         rest <- compileStmt body (return . mkLast . Done name label)
>         addProg (mkFirst (BlockEntry name label args) <*> rest)
>     -- Create initial locations for all top level functions.
>     initialDefs :: (Int, Map Name (Maybe Dest))
>     initialDefs = 
>       let top = execState (mapM_ mkDest defs) (mkC 200 Map.empty)
>           mkDest :: Def -> CompM ()
>           mkDest (name, _) = withNewLabel $ \label -> do
>             modify (\s@(C { compT }) -> s { compT = Map.insert name (Just (name, label)) compT })
>           primDest :: StmtM C O -> Map Name (Maybe Dest) -> Map Name (Maybe Dest)
>           primDest entry topMap = 
>             let (name, label) = destOfEntry entry
>             in Map.insert name (Just (name, label)) topMap
>       in (compI top, foldr primDest (compT $ top) (map snd . entryPoints $ predefined))
>     -- | Create the initial state for our compiler.
>     mkC i tops = C i emptyClosedGraph tops []
>     

> -- | Compiler state. 
> data CompS = C { compI :: Int -- ^ counter for fresh variables
>                , compG :: ProgM C C -- ^ Program control-flow graph.
>                , compT :: Map Name (Maybe Dest)  -- ^ top-level function names and their location.
>                , compF :: [Name] } -- ^ Currently free variables.

              
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

> -- | Gets free variables in the expression.
> getFree :: Expr -> CompM [Name]
> getFree expr = return (free expr)

> -- | Gets the currently known free variables.
> currFree :: CompM [Name]
> currFree = gets compF

> -- | Sets the currently known free variables.
> setFree :: Expr -> CompM [Name]
> setFree expr = do
>   modify (\s@(C { compF }) -> s { compF = free expr })
>   gets compF

> -- Determine if the name represents
> -- a top level function and return
> -- the location of that function, if so.
> isTopLevel :: Name -> CompM (Maybe Dest)
> isTopLevel name = do
>   free <- currFree
>   if name `elem` free
>    then gets compT >>= return . maybe Nothing id . Map.lookup name 
>    else return Nothing

> -- | Modifies the free variables using the update function, then
> -- passes the new list of free variables to the action given. Top-level
> -- free variables are removed from the list, as well.
> withFree :: ([Name] -> CompM [Name]) -> ([Name] -> CompM a) -> CompM a
> withFree upd p = do
>   oldfvs <- gets compF
>   fvs <- upd oldfvs
>   tops <- gets compT >>= return . Map.keys
>   modify (\s@(C { compF }) -> s { compF = fvs})
>   a <- p (fvs \\ tops)
>   modify (\s@(C { compF }) -> s { compF = oldfvs })
>   return a

> usingFree :: [Name] -> CompM a -> CompM a
> usingFree fvs p = withFree (const (return fvs)) (\_ -> p)

> free :: Expr -> Free
> free = nub . free'
>   where
>     free' (EVar (Ident v _) _) = [v]
>     free' (EPrim (Ident v _) _ _) = [v]
>     free' (ENat _) = []
>     free' (EBits _ _) = []
>     free' (ECon _ _) = []
>     free' (ELam (Ident v _) _ expr) = v `delete` nub (free' expr)
>     free' (ELet (Decls decls) expr) = 
>             (free' expr \\ 
>                    map (\(Defn (Ident n _) _ _) -> n) (getDefns decls)) ++ 
>             (nub $ concatMap freeDefn $ getDefns decls)
>     free' (ECase expr alts) = nub (free' expr ++ concatMap (\(LC.Alt _ _ vs e) -> nub (free' e) \\ map (\(Ident n _) -> n) vs) alts)
>     free' (EApp e1 e2) = nub (free' e1 ++ free' e2)
>     free' (EFatbar e1 e2) = nub (free' e1 ++ free' e2)
>     free' (EBind (Ident v _) _ e1 e2) = nub (free' e1 ++ v `delete` nub (free' e2))
>     declName (Defn (Ident n _) _ _) = n
>     freeDefn (Defn (Ident n _) _ (Right e)) = n `delete` nub (free' e)
>     freeDefn (Defn (Ident n _) _ _) = []

> setDest :: Name -> Label -> CompM ()
> setDest name label = 
>   modify (\s@(C { compT }) -> s { compT = Map.insert name (Just (name, label)) compT })

> getDestOfName :: Name -> CompM (Maybe Dest)
> getDestOfName name = gets compT >>= return . fromMaybe Nothing . Map.lookup name

> -- | Add a program (C C block) to the list of blocks
> -- maintained by the monad.
> addProg :: ProgM C C -> CompM ()
> addProg block = modify (\s@(C { compG }) -> s { compG = block |*><*| compG })

> -- | Do something with a new label.
> withNewLabel :: UniqueMonad m => (Label -> m a) -> m a
> withNewLabel f = freshLabel >>= f
  
> toAlt :: LC.Alt -> Alt Expr
> toAlt (LC.Alt (Ident cons _) _ vs expr) = Alt cons (map (\(Ident n _) -> n) vs) expr

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

> mkName :: Name -> Name -> Name
> mkName prefix name  
>   | prefix `isInfixOf` name = name
>   | otherwise = prefix ++ name

> fromProgram :: Program -> [(Name, Expr)]
> fromProgram (Program { decls = (Decls d)}) = [(name, expr) | decl <- d, (Defn (Ident name _) _ (Right expr)) <- f decl] 
>   where
>     f (Mutual decls) = decls
>     f (Nonrec decl) = [decl] 
    
> mkBind :: Name -> Label -> Name -> TailM -> TailM -> CompM (ProgM O C)
> mkBind n l r f t = return (mkMiddle (Bind r t) <*> mkLast (Done n l f))

