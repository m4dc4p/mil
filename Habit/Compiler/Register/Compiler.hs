{-# LANGUAGE ScopedTypeVariables #-}
module Habit.Compiler.Register.Compiler

where

import Data.List (lookup, intercalate, (\\), nub, elemIndex)
import Control.Monad.Writer
import Control.Monad.State
import Data.Maybe (fromJust, isJust, catMaybes, maybeToList)
import Data.Supply
import Data.Graph.SCC(stronglyConnComp)
import Data.Graph(SCC(..))
import Data.Map (Map)
import qualified Data.Map as Map

import Habit.Syntax.AST hiding (Label)
import Habit.Syntax.Names (Name(..), qual)
import qualified Habit.Syntax.Utils as U
import Habit.Syntax.Utils (DeclSCC(..), decl_deps)

import Habit.Compiler.Register.Machine (Instr, Reg, Field)
import qualified Habit.Compiler.Register.Machine as H -- H for hardware

-- | Code is a labeled list of instructions.
type Code = (Label, [Instr])

-- | Specify how to label lists of instructions. 
type Label = String 

-- | A group represents a function body, more or less.  First element
--  is the Label of the code element which is the entry point for the
--  group.  Second element is the number of arguments expected in the
--  closure when the entry point code element is executed. Third
--  element is the code making up the group.
type Group = (Label, Int, [Code])

-- | State we need during compilation. nextID gives us
-- unique integers for labels and registers. inProgress is 
-- a stack of Group defintions, indicating which Groups are
-- still being recorded. completed indicates Groups that have
-- been recorded completely.
data S = S { nextID :: Supply Int 
           , inProgress :: [Group]
           , completed :: [Group] }

-- | Our compiler monad - we just carry around some state.
type C = State S 

-- | Create a unique label.
newLabel :: C String
newLabel = do
  m <- get
  let (s1, s2) = split2 . nextID $ m
  put m { nextID = s2 }
  -- As long as this prefix is unique, labels
  -- produced here won't collide with assembler.
  return $ "lab" ++ show (supplyValue s1)

-- | Create a unique label with the given name embedded.
newNamedLabel :: String -> C String
newNamedLabel name = do
  m <- get
  let (s1, s2) = split2 . nextID $ m
  put m { nextID = s2 }
  -- As long as this prefix is unique, labels
  -- produced here won't collide with assembler.
  return $ "lab" ++ (replace '.' '_' name) ++ show (supplyValue s1)

-- | Create a unique register.
newReg :: C Reg
newReg = do
  m <- get
  let (s1, s2) = split2 . nextID $ m
  put m { nextID = s2 }
  return $ "reg" ++ show (supplyValue s1)

-- | Create a unique register with the given name embeded.
newNamedReg :: Name -> C Reg
newNamedReg name = do
  m <- get
  let (s1, s2) = split2 . nextID $ m
  put m { nextID = s2 }
  return $ "reg" ++ (replace '.' '_' (showName name)) ++ show (supplyValue s1)

-- | Create a unique, globally persistent register, with the name
-- given embedded.
newGlobalReg :: Name -> C Reg
newGlobalReg name = do
  m <- get
  let (s1, s2) = split2 . nextID $ m
  put m { nextID = s2 }
  return $ "glob" ++ (replace '.' '_' (showName name)) ++ show (supplyValue s1)


-- | Begins tracking instructions for a new code group.
newGroup :: Int -> ([Reg] -> C [Instr]) -> C Label
newGroup size action = do
    label <- newLabel
    let prologue = 
          let mkReg i = do 
                t <- newReg
                return (t, H.Load (H.cloReg, i) t)
          in mapM mkReg [0 .. size - 1] >>= return . unzip
    (regs, init) <- prologue
    modify (\s -> s { inProgress = (label, size, []) : (inProgress s) })
    body <- action regs
    let addEntry s@(S { inProgress = (l, i, c) : rest
                      , completed = comp }) 
            = s { inProgress = rest
                , completed = (l, i, (label, init ++ body) : c) : comp }
    modify addEntry
    return label

-- | Record a labeled block of code.    
record :: String -> [Instr] -> C ()
record l instrs = do
    modify addCode
  where
    code = (l, instrs)
    addCode s@(S { inProgress = [] }) 
        = error $ "Not able to record right now!"
    addCode s@(S { inProgress = (l, i, cs) : css }) 
        = s { inProgress = (l, i, code : cs) : css }

-- | Compile a module to a list of "group" blocks. 
compile :: Supply Int -> Module -> [Group]
compile supply m 
    = let ((finalReg, init), S _ _ completed) = runState compileTop (S supply [] [])
          lastInstr = maybe H.Halt H.Ret finalReg
      in ("TOP", 0, [("TOP", init ++ [lastInstr])]) : completed
  where
    -- Place module data constructors into
    -- the initial environment
    compileTop :: C (Maybe Reg, [Instr])
    compileTop = do
      let datas = mod_data m
          decls = decl_deps . mod_decls $ m
      (env, dataInit) <- compileDatas datas [] 
      (env', declInit)  <- compileDecls decls env
      let mainReg = lookup (qual (mod_name m) "main") env' 
      return (mainReg,dataInit ++ declInit)

-- | Extract and concatenate all instructions from a list of
-- function blocks. Labels are added as needed.
getInstrs :: [Group] -> [Instr]
getInstrs groups = concatMap snd . concatMap third . map addLabels $ groups
    where
      third (a,b,c) = c
      addLabels :: Group -> Group
      addLabels (entry, size, blocks) = 
          let blocks' = map (\(l, b) -> (l, H.Label l : b)) blocks
          in (entry, size, blocks')

-- | An environment is a list of name & location pairs.
type Env = [(Name, Reg)]

-- | Compile a list of declarations. The list of declarations
-- are given as strongly-connected components. Mutually recursive
-- definitions will be compiled together. We return an environment
-- with new bindings.
compileDecls :: [DeclSCC] -> Env -> C (Env, [Instr])
compileDecls decls env = do
  let cdM (e, inits) (Rec recDecls) = do
        -- All strongly connected components must be compiled together, 
        -- so we get their names into the environment all at once.
        let makeEnv d = do 
              let name = decl_name d
              r <- if isGlobal name 
                    then newGlobalReg name 
                    else newNamedReg name
              l <- newNamedLabel "makeEnv"
              return (decl_name d, r)
            f env (dst, decl) = compileDecl env dst decl
            decl_bodies = (impl_decls recDecls ++ map decl (expl_decls recDecls))
        env' <- mapM makeEnv decl_bodies
        let env'' = env' ++ e
            decl_dests = [(fromJust $ lookup (decl_name d) env'', d) | d <- decl_bodies]
        (allocs, init) <- mapM (f env'') decl_dests >>= return . unzip
        -- We ensure allocations happen first for mutually recursive functions.
        return (env' ++ e, inits ++ (catMaybes $ allocs) ++ concat init)
      cdM (e, inits) dscc = do
        let d = case dscc of
                  NonRecImpl impl -> impl
                  NonRecExpl expl -> (decl expl)
            name = decl_name d
        dst <- if isGlobal name 
                then newGlobalReg name 
                else newNamedReg name
        (allocC, init) <- compileDecl e dst d
        return ((decl_name d, dst) : e, maybeToList allocC ++ inits ++ init)
      -- | Compile an individual implementation
      -- declaration.
      compileDecl :: Env -> Reg -> ImplDecl -> C (Maybe Instr, [Instr])
      compileDecl e dest decl = do 
        let name = decl_name decl
        (_, allocC, matchC) <- compileMAbs e (Just dest) (Just name) Abort (decl_body decl)
        return (allocC, mkN ("compileDecl: " ++ showName name) : matchC)
  foldM cdM (env, []) decls


-- | Compile each constructor to a function which will
-- create that data. 
compileDatas :: [Data] -> Env -> C (Env, [Instr])
compileDatas dataDefs env = do
    let mkData 1 (name, count) regs = do
          result <- newNamedReg name
          let loads = map (\(r, i) -> H.Store r (result, i)) . zip regs $ [0..]
          return $ H.AllocD result (showName name) count :
                   loads ++ [H.Store H.argReg (result, count - 1)
                            , H.Ret result]
        mkData remain def@(name, _) regs = do
          r <- newNamedReg name
          entry <- newGroup (length regs + 1) $ mkData (remain - 1) def
          closureC <- mkClosure r entry regs
          return $ mkN "mkData n" : closureC ++ [H.Ret r]
        compileData (e, inits) (name, 0) = do
          -- We create global registers in the two cases below
          -- because the entry point to the data constructor should
          -- always be global.
          r <- newGlobalReg name
          return ((name, r) : e
                 , mkN ("compileData 0: " ++ showBinding (name, r))
                   : H.AllocD r (showName name) 0 : inits)
        compileData (e, inits) (name, count) = do
          r <- newGlobalReg name
          entry <- newGroup 0 $ mkData count (name, count)
          return ((name, r) : e
                 , mkN ("compileData n: " ++ showBinding (name, r))
                   : H.AllocC r entry 0 : inits)
    foldM compileData (env, []) constructors
  where
    constructors = map mkPair . concatMap data_cons $ dataDefs
    countFields = length . qual_body . data_con_fields 
    mkPair con = (data_con_name con, countFields con)



-- | What to do when a match fails: abort or jump
-- to a label.
data OnFail = Abort 
   | OnFail Label
 deriving (Show)

-- | Code to execute after a match has succeeded
type Success = [Instr]

-- | Description of what to do when a match
-- finishes, either through success or 
-- failure.
data MatchDone = MD OnFail Success
  deriving (Show)

-- | Generate appropriate instructions based on
-- failure mode.
handleFailure :: OnFail -> [Instr]
handleFailure Abort = [H.Error "Match failure!"]
handleFailure (OnFail l2) = [H.Jmp l2]

-- | A match takes an environment, a description of what to do when
-- the match succeeds or what to do when it fails and a list of
-- "arguments". The argument list tells the match where to find the
-- values it is matching against. They will be consumed in the order
-- given. 
--
-- compileMatch returns a register where the result of the match
-- is stored and the instructions necessary for starting the match.
compileMatch :: Env -> MatchDone -> Reg -> Match -> [Reg] -> C [Instr]

-- A match pattern binds variables and evaluates its body
-- in the new environment. One argument is consumed when 
-- binding.
compileMatch env m@(MD failure _) result (MPat pat body) (arg:args) = do
  (env', patC) <- compilePat env failure pat arg
  bodyC <- compileMatch env' m result body args
  let note = mkN "compileMatch: MPat"
  return $ note : patC ++ bodyC

-- A match guard evaluates the guard and creates
-- a new environment, if the guard succeeds. The body
-- is then evaluated in the new environment.
compileMatch env m@(MD failure success) result (MGrd guard body) args = do
  (env', guardC) <- compileGuard env failure guard 
  bodyC <- compileMatch env' m result body args
  let note = mkN "compileMatch: MGrd"
  return $ note : guardC ++ bodyC ++ success

-- MAlt evaluates the first match and, if it fails,
-- evaulates the second match. If the second match
-- fails, the match fails. If either match succeeds
-- the result will be in the register returned.
compileMatch env (MD failure success) result (MAlt alt1 alt2) args = do
  (l1:l2:_) <- mapM (const newLabel) [0..1]
  alt1C <- compileMatch env (MD (OnFail l2) success) result alt1 args
  alt2C <- compileMatch env (MD failure success) result alt2 args
  record l2 (mkN "compileMatch: MAlt2" : alt2C)
  return $ mkN "compileMatch: MAlt1" : alt1C 

-- A "pure" match expression. Always succeeds and
-- puts its result in the register returned.
compileMatch env (MD _ success) result (MExp expr) _ = do
  (resultE, exprC) <- compileExpr env expr
  let note = mkN "compileMatch: MExp" 
  return $ note : exprC ++ H.Copy resultE result : success

compileMatch _ (MD failure _) _ (MFail arity) _ = 
  return $ handleFailure failure

compileMatch e md r expr args = error $ "Pattern match failure\n e: " ++ show e ++
                           "\n md: " ++ show md ++ "\n r: " ++ show r ++ 
                           "\n args: " ++ show args ++
                           "\n expr: " ++ show expr

-- | A pattern is compiled with a given environment
-- and failure mode. The location for the value to 
-- pattern-match against is also given. A pattern
-- returns a new environment and instructions necessary
-- to evaluate the pattern.
compilePat :: Env -> OnFail -> Pat -> Reg -> C (Env, [Instr])

-- PVar pattern simply binds a name to the 
-- location given.
compilePat env _ (PVar name) arg = do
  let note = [mkN ("compilePat: PVar (" ++ showName name ++ 
                    " : " ++ show arg ++ ")")]
  return ((name, arg) : env, note)

-- PCon determines if the location given 
-- matches the constructor given. The arguments
-- to the constructor get bound to names in the
-- new environment, if the pattern-match succeeds.
compilePat env f (PCon name _ pats) arg = do
  let next (l, o) = (l, (o + 1))
      bindArgs (l, e, is) p = do
        tmp <- newReg
        (e', is') <- compilePat e f p tmp
        return (next l, e', is ++ H.Load l tmp : is')
  (_, env', patC) <- foldM bindArgs ((arg, 0), env, []) pats
  l1 <- newLabel
  l2 <- newLabel
  record l1 (handleFailure f)
  record l2 patC
  let note = mkN "compilePat: PCon" 
  return (env', note : [H.FailT arg (showName name) (H.F l1) (H.S l2)])

-- A pattern guard evaulates the guard and, if
-- it succeeds, matches against the pattern given. 
compilePat env f (PGrd p g) arg = do
  (env', guardC) <- compileGuard env f g 
  (env'', patC) <- compilePat env' f p arg
  let note = mkN "compilePat: PGrd" 
  return (env''
         , note : guardC ++ patC)

-- A pattern signature has no runtime effect
-- and just evaluates to the underlying
-- pattern given.
compilePat env f (PSig pat typ) arg = compilePat env f pat arg

-- A pattern wildcard always succeeds and
-- matches everyting. That is, it has no
-- effect.
compilePat env _ PWild _ = return (env, [mkN "compilePat: PWild"])

-- | A guard checks an expression against a pattern and 
-- can also create new bindings. A guard always returns
-- a new environment and instructions for executing
-- the guard.
compileGuard :: Env -> OnFail -> Guard -> C (Env, [Instr])

-- A GMatch checks an expression against a pattern 
-- and fails if the pattern does not match. Otherwise,
-- execution continues.
compileGuard env f (GMatch pat expr) = do
  (regE, exprC) <- compileExpr env expr
  (env', testC) <- compilePat env f pat regE
  return (env', mkN "compileGMatch" : exprC ++ testC)

-- GLet binds new values in the environment.
compileGuard env failure (GLet decls) = do
  (env', initC) <- compileDecls (decl_deps decls) env
  return (env', mkN "compileGLet" : initC)

-- | Compile a pure expression. Compiling an expression in an
-- environment always results in a register holding the final value
-- and instructions for the evaulation.
compileExpr :: Env -> Expr -> C (Reg, [Instr])

compileExpr env (EApp expr1 expr2) = do
  result <- newReg
  (t2, expr2C) <- compileExpr env expr2
  (t1, expr1C) <- compileExpr env expr1
  return (result
         , expr2C ++ expr1C ++ 
           [mkN "EApp", H.Enter t1 t2 result])

compileExpr env (ELet decls expr) = do
  (env', initC) <- compileDecls (decl_deps decls) env
  (result, exprC) <- compileExpr env' expr
  return (result
         , mkN "ELet" : initC ++ exprC)

compileExpr env (EAbs match) = do
  (result, allocC, matchC) <- compileMAbs env Nothing Nothing Abort match
  return (result
         , mkN "EAbs" 
           : maybeToList allocC ++ matchC)

compileExpr env (ECase expr match) = 
  compileExpr env (EApp (EAbs match) expr)

compileExpr env (EInfix expr1 name expr2) = error "EInfix"
compileExpr env (EParens expr) = error "EParens" 

compileExpr env (EVar (EV name _ _)) = 
  return $ case lookup name env of
             Just l -> (l, [mkN ("EVar: " ++ showName name ++ " = " ++ show l)])
             _ -> error $ "Can't lookup var name " ++ showName name ++ " in " ++ show env

compileExpr _ (ELit literal) = do
  let showLit (LNum i) = show i
      showLit (LFrac r) = show r
      showLit (LChar c) = [c]
      showLit (LString s) = s 
  result <- newReg
  return (result
         , [H.Set result (H.Str . showLit $ literal)])


-- | Compile a match like an abstraction. A match is treated like an
-- abstraction and is compiled in a particular environment, with a
-- given failure mode. An optional argument can be given, which will
-- be consumed by the match. Because a match can create bindings, we
-- may compile a series of closures to get all arguments to the
-- match. We return a location for the result of the match, allocation
-- instructions (if any) and instructions necessary to evaluate the
-- match.
--
-- Allocation instructions are returned to support mutually recursive,
-- locally defined functins. We must allocate all storage before
-- loading any free variables.
compileMAbs :: Env -> Maybe Reg -> Maybe Name -> OnFail -> Match -> C (Reg, Maybe Instr, [Instr])
compileMAbs env dest name f m = do
  result <- case (dest, name) of
              (Just r, _) -> return r
              (Nothing, Just n) -> newNamedReg n
              (_, _) -> newReg
  case countParams m of
    0 -> do
      matchC <- compileMatch env (MD f []) result m []
      return (result, Nothing
             , mkN "compileMAbs 0" 
               : mkN ("dest is: " ++ show dest) 
               : matchC)
    nparams -> do
      let fvs     = [fv | fv <- U.fvs m
                    , not $ isGlobal fv] -- This condition make sure top
                                         -- level declarations are not 
                                         -- considered free.
          fvRegs  = [r | Just r <- map (flip lookup env) fvs]
          fvLoads = map (\(r, i) -> H.Store r (result, i)) . zip fvRegs $ [0..]
      l <- compileAbs env f nparams fvs m 
      return (result, Just $ H.AllocC result l (length fvRegs)
             , mkN ("free: " ++ showNames fvs ++ ", env: " ++ showEnv env) 
               : mkN ("dest is: " ++ show dest) 
               : fvLoads)
  where
    -- Calculate maximum parameters required by a match.
    countParams :: Match -> Int
    countParams (MPat _ m) = 1 + countParams m
    countParams (MGrd _ m) = countParams m
    countParams (MAlt m1 m2) = max (countParams m1) (countParams m2)
    countParams _ = 0

-- | Compiles intermediate instructions for consuming arguments
-- and copying them between closures, until all arguments have
-- been consumed and the function can do real work.   
compileAbs env f nparams fvs m = newGroup nfvs $ compileAbs' 1
  where
    nfvs = length fvs
    compileAbs' n regs 
      | n == nparams = do
          let (fvRegs, argRegs) = splitAt nfvs regs
              env' = zip fvs fvRegs ++ env
              args' = argRegs ++ [H.argReg]
          r <- newReg
          l <- newLabel
          record l [H.Ret r]
          matchC <- compileMatch env' (MD f [H.Jmp l]) r m args'
          return $ mkN "compileAbs 1" : matchC
      | otherwise = do
          entry <- newGroup (length regs + 1) $ compileAbs' (n + 1)
          r <- newReg
          closureC <- mkClosure r entry regs
          return $ mkN "compileAbs n" 
                     : closureC ++ [H.Ret r]

-- | Create a closure in the register given, for the
-- label specified. The list of registers passed will be
-- copied into the closure in order. Additionally, the 
-- argument register is copied into the closure.
mkClosure :: Reg -> String -> [Reg] -> C [Instr]
mkClosure dst label argRegs = do
  let loads = map (\(r, i) -> H.Store r (dst, i)) . zip (argRegs ++ [H.argReg]) $ [0..]
  return $ H.AllocC dst label (length loads) : loads 

-- | Show a list of names nicely.
showNames :: [Name] -> String
showNames = intercalate "," . map showName

-- | Readably print a name.
showName (Name (Just m) name _) = mkPrefix m ++ "." ++ name
  where
    mkPrefix (ModName [] last) = last
    mkPrefix (ModName pres last) = foldr1 (\a rest -> a ++ "." ++ rest) pres ++ "." ++ last
showName (Name _ name _) = name

-- | Indicates if a name should be treated globally or not. Global names
-- are module qualified. 
isGlobal :: Name -> Bool
isGlobal name = isJust (qualifier name)

-- | Print an environment
showEnv :: Env -> String
showEnv env = "[" ++ intercalate "," (map showBinding env) ++ "]"

-- | Print a single environment binding
showBinding :: (Name, Reg) -> String
showBinding (n, l) = "(" ++ showName n ++ ", " ++ show l ++")"

-- | Add a note instruction.
mkN :: String -> Instr
mkN = H.Note

-- | Replace the first argument with the second in 
-- the list of items given.
replace a b ls = 
    let rep x
            | x == a = b
            | otherwise = x
    in map rep ls
                     
