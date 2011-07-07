{-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
  , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}

module MIL

where

import Prelude hiding (abs)
import Control.Monad (liftM)
import Control.Monad.State (State, execState, modify, gets)
import Text.PrettyPrint 
import Data.List (sort)
import Data.Maybe (fromMaybe, isJust, catMaybes, fromJust)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Compiler.Hoopl

import Util

type ProgM = Graph StmtM
type Dest = (Name, Label)

{-

Our monadic language:

  
  bodyM ::= do 
    stmtM1; 
    ... ; 
    stmtMN; 
    tailM

  stmtM ::= v <- tailM
    | case v of [alt1, ..., altN]
    | return tailM

  tailM ::= return v
    | v1 @ v2         -- Call an unknown function.
    | f(v1, ..., v)  -- Goto a known block.
    | closure f {v1, ..., vN} -- Create closure pointing to a function.
    | ... undocumented statements ...

  alt ::= C v1 ... vN -> call f(u1, ..., uM)

  defM ::= f {v1, ..., vN} v = bodyM -- ``f'' stands for the name of the function.

  progM :: defM1
           ...
           defMN
-}

data StmtM e x where
  -- | Entry point to a block.
  BlockEntry :: Name -- Name of the block
    -> Label    -- Label of the entry point.
    -> [Name] -- arguments
    -> StmtM C O

  -- | Entry point to a closure-capturing block.
  CloEntry :: Name -- Name of the block
    -> Label    -- Label of the entry point.
    -> [Name]   -- Variables in closure
    -> Name     -- argument
    -> StmtM C O
  
  Bind :: Name      -- Name of variable that will be bound.
    -> TailM    -- Expression that computes the value we want.
    -> StmtM O O    -- Open/open since bind does not end an expression
  
  CaseM :: Name      -- Variable to inspect
    -> [Alt TailM] -- Case arms
    -> StmtM O C
      
  Done :: Name -- ^ Name of this block
    -> Label -- ^ Label of this block
    -> TailM  -- Finish a block.
    -> StmtM O C

-- | TailM concludes a list of statements. Each block ends with a
-- TailM except when CaseM ends the blocks.
data TailM = Return Name 
  | Enter -- ^ Enter a closure.
    Name  -- ^ Variable holding the closure.
    Name  -- ^ Argument to the function.
  | Closure -- ^ Create a closure.
    Dest    -- ^ Label for the function held by the closure.
    [Name]  -- ^ List of captured free variables.
  | Goto   -- ^ Jump to a block.
    Dest   -- ^ Address of the block
    [Name] -- ^ Arguments/live variables used in the block.
  | ConstrM     -- ^ Create a data value.
    Constructor -- ^ Constructor name.
    [Name]      -- ^ Only variables allowed as arguments to
                -- constructor.
  | Thunk  -- ^ Monadic thunk - suspended computation.
    Dest   -- ^ Label of the computation's body.
    [Name] -- ^ Free variables in the body.
  | Run  -- ^ Execute a monadic computation.
    Name  -- ^ Variable holding the thunk
  | Prim    -- ^ Execute a primitive block 
    Name    -- ^ Name of the primitive
    [Name]  -- ^ Arguments to the primitive
  | LitM    -- ^ Numeric value
    Integer 
  deriving (Eq, Ord, Show)

-- Pretty printing programs
printStmtM :: StmtM e x -> Doc
printStmtM (Bind n b) = text n <+> text "<-" <+> nest 2 (printTailM b)
printStmtM (BlockEntry f _ args) = text f <+> 
                                  parens (commaSep text args) <> text ":" 
printStmtM (CloEntry f _ clos arg) = text f <+> braces (commaSep text clos) 
                                     <+> text arg <> text ":" 
printStmtM (CaseM v alts) = hang (text "case" <+> text v <+> text "of") 2 (vcat' $ map printAlt alts)
  where
    printAlt (Alt cons vs tailM) = text cons <+> hsep (texts vs) <+> text "->" <+> printTailM tailM
printStmtM (Done _ _ t) = printTailM t

printTailM :: TailM -> Doc
printTailM (Return n) = text "return" <+> text n
printTailM (Enter f a) = text f <+> text "@" <+> text a
printTailM (Closure dest vs) = text "closure" <+> printDest dest <+> braces (commaSep text vs)
printTailM (Goto dest vs) = printDest dest <> parens (commaSep text vs)
printTailM (ConstrM cons vs) = text cons <+> (hsep $ texts vs)
printTailM (Thunk dest vs) = text "thunk" <+> printDest dest <+> brackets (commaSep text vs)
printTailM (Run v) = text "invoke" <+> text v
printTailM (Prim p vs) = text p <> text "*" <> parens (commaSep text vs)
printTailM (LitM n) = text ("num " ++ show n)

printDest :: Dest -> Doc
printDest (name, _) = text name

printProgM :: ProgM C C -> Doc
printProgM = vcat' . maybeGraphCC empty printBlockM

printBlockM = p . blockToNodeList'
  where p (e, bs, x) = hang (maybeC empty printStmtM e) 2
                       (vcat' (map printStmtM bs) $+$
                        maybeC empty printStmtM x)
instance NonLocal StmtM where
  entryLabel (BlockEntry _ l _) = l
  entryLabel (CloEntry _ l _ _) = l
  successors = stmtSuccessors
                        
stmtSuccessors :: StmtM e C -> [Label]
stmtSuccessors (CaseM _ alts) = [l | (Alt _ _ (Goto (_, l) _)) <- alts]
stmtSuccessors (Done _ _ (Goto (_, l) _)) = [l]
stmtSuccessors _ = []

tailSuccessors :: TailM -> [Dest]
tailSuccessors (Goto dest _) = [dest]
tailSuccessors _ = []

tailDest :: TailM -> [Dest]
tailDest (Closure dest _) = [dest]
tailDest (Thunk dest _) = [dest]
tailDest (Goto dest _) = [dest]
tailDest _ = []

-- Utility functions

-- | Get all the labels at entry points in 
-- the program.
entryPoints :: ProgM C C -> [(Label, StmtM C O)]
entryPoints (GMany _ blocks _) = map getEntryLabel (mapElems blocks)

-- | Get all entry labels in a program.
entryLabels :: ProgM C C -> [Label]
entryLabels = map fst . entryPoints 

-- | Entry label of a block, pllus the entry instruction.
getEntryLabel :: Block StmtM C x -> (Label, StmtM C O)
getEntryLabel block = case blockToNodeList' block of
  (JustC e@(BlockEntry _ l _), _, _) -> (l, e)
  (JustC e@(CloEntry _ l _ _), _, _) -> (l, e)

-- | Find a block with a given label in the propgram
-- and return it paired with it's label and name.
blockOfLabel :: ProgM C C -> Label -> Maybe (Dest, Block StmtM C C)
blockOfLabel body l = case lookupBlock body l of
                  BodyBlock block -> Just (blockToDest block)
                  _ -> Nothing

destOfEntry :: StmtM C O -> Dest
destOfEntry (BlockEntry n l _) = (n, l)
destOfEntry (CloEntry n l _ _) = (n, l)

-- | Constructin destination label for a given block.
blockToDest :: Block StmtM C C -> (Dest, Block StmtM C C)
blockToDest block = (destOfEntry (blockEntry block), block)

-- | Get the first instruction in a block.
blockEntry :: Block StmtM C C -> StmtM C O
blockEntry b = case blockToNodeList' b of
                 (JustC entry, _, _) -> entry


-- | Find destinatino for a given label, if
-- it exists.
labelToDest :: ProgM C C -> Label -> Maybe Dest
labelToDest prog l = maybe Nothing (Just . fst) (blockOfLabel prog l)

-- | Pair all blocks with their destination.    
allBlocks :: ProgM C C -> [(Dest, Block StmtM C C)]
allBlocks (GMany _ blocks _) = map blockToDest (mapElems blocks)

-- | Get the tail of a block. Will exclude
-- the entry instruction (if C C) or the
-- first instruction in the block (O C)
blockTail :: Block StmtM x C -> ProgM O C
blockTail b = case blockToNodeList' b of
                (_, mid, JustC end) -> mkMiddles mid <*> mkLast end


-- | Find all successors (to all possible depths) for
-- each block in the program.
allSuccessors :: ProgM C C -> Map Dest (Set Dest)
allSuccessors prog = 
    Map.fromList . 
    map (\(d, ds) -> (d, allSucc ds Set.empty)) $
    blocksToDests 
  where
    -- | Map each block to its immediate successors, if any.
    destToSucc :: Map Dest [Dest]
    destToSucc = Map.fromList blocksToDests
    blocksToDests = map f (allBlocks prog)
    f (dest, block) = (dest, map (fromJust . labelToDest prog) (successors block))
    -- | Find all successors starting with a given list of 
    -- blocks.
    allSucc [] s = s
    allSucc (d:ds) s 
      | not (d `Set.member` s) = allSucc (fromMaybe [] (Map.lookup d destToSucc) ++ ds) (Set.insert d s)
      | otherwise = allSucc ds s

-- | Create a Done statement if a Tail is given.
done :: Monad m => Name -> Label -> Maybe TailM -> m (Maybe (ProgM O C))
done n l = return . maybe Nothing (Just . mkLast . Done n l)

-- | Create a Bind statement if a Tail is given.
bind :: FuelMonad m => Name -> Maybe TailM -> m (Maybe (ProgM O O))
bind v = return . maybe Nothing (Just . mkMiddle . Bind v)

-- | Create a case statement if alts are given.
_case :: FuelMonad m => Name -> (Alt TailM -> Maybe (Alt TailM)) -> [Alt TailM] -> m (Maybe (ProgM O C))
_case v f alts  
  | any isJust alts' = return $ Just $ mkLast $ CaseM v (zipWith altZip alts alts')
  | otherwise = return $ Nothing
  where
    alts' = map f alts
    altZip _ (Just a) = a
    altZip a _ = a

nameOfEntry :: StmtM C O -> Name
nameOfEntry = fst . destOfEntry

-- Primitives

primNames :: [Name]
primNames = map fst p
  where
    p :: [(Name, SimpleUniqueMonad (ProgM C C))]
    p = prims

compiledPrims :: UniqueMonad m => [(Name, m (ProgM C C))] -> m [(Name, ProgM C C)]
compiledPrims [] = return []
compiledPrims ((n, m):ms) = do
  head <- m
  rest <- compiledPrims ms
  return ((n, head):rest)
  
prims :: UniqueMonad m => [(Name, m (ProgM C C))]
prims = [plusPrim
        , minusPrim
        , timesPrim
        , divPrim
        , ltPrim
        , gtPrim
        , ltePrim
        , gtePrim
        , eqPrim
        , neqPrim
        , printPrim 
        , ("mkData_Nil", mkDataPrim "Nil" 0)
        , ("mkData_Cons", mkDataPrim "Cons" 2)
        , ("mkData_Unit", mkDataPrim "Unit" 0)] ++ prioSetPrims
  where
    -- Primitives necessary to compile PrioSetLC.lhs in ..\..priosetExample
    prioSetPrims = 
      [("readRef", liftM snd $ monadic unaryPrim "readRef")
      ,("primBitwiseDecIx", liftM snd $ monadic unaryPrim "primBitwiseDecIx")
      ,("primIxShiftR", liftM snd $ monadic binPrim "primIxShiftR")
      ,("primIxLt", liftM snd $ monadic binPrim "primIxLt")
      ,("primBitwiseModIx", liftM snd $ monadic unaryPrim "primBitwiseModIx")
      ,("primUnsignedPlus", liftM snd $ monadic binPrim "primUnsignedPlus")
      ,("primIxToUnsigned", liftM snd $ monadic unaryPrim "primIxToUnsigned")
      ,("primUnsignedTimes", liftM snd $ monadic binPrim "primUnsignedTimes")
      ,("primLeqIx", liftM snd $ monadic binPrim "primLeqIx")
      ,("constructBitdata", liftM snd $ monadic unaryPrim "constructBitdata")
      ,("primBoolNot", liftM snd $ monadic unaryPrim "primBoolNot")
      ,("primIxEq", liftM snd $ monadic binPrim "primIxEq")
      ,("primUnsignedMinus", liftM snd $ monadic binPrim "primUnsignedMinus")
      ,("primKReturn", liftM snd $ monadic unaryPrim "primKReturn")
      ,("primUnsignedFromLiteral", liftM snd $ monadic unaryPrim "primUnsignedFromLiteral")
      ,("primIxFromLiteral", liftM snd $ monadic unaryPrim "primIxFromLiteral")
      ,("initArray", liftM snd $ monadic binPrim "initArray")
      ,("primInitStored", liftM snd $ monadic binPrim "primInitStored")
      ,("@", liftM snd $ monadic binPrim "@")
      ,("writeRef", liftM snd $ monadic binPrim "writeRef")
      ,("mkData_False", mkDataPrim "False" 0)
      ,("mkData_True", mkDataPrim "True" 0)]
  


printPrim, plusPrim, minusPrim, timesPrim, divPrim, ltPrim, gtPrim, ltePrim, gtePrim, eqPrim, neqPrim :: UniqueMonad m => (Name, m (ProgM C C))

printPrim = ("print", liftM snd $ monadic unaryPrim "print")

plusPrim = ("plus", liftM snd $ binPrim "plus")
minusPrim = ("minus", liftM snd $ binPrim "minus")
timesPrim = ("times", liftM snd $ binPrim "times")
divPrim = ("div", liftM snd $ binPrim "div")

ltPrim = ("lt", liftM snd $ binPrim "lt")
gtPrim = ("gt", liftM snd $ binPrim "gt")
ltePrim = ("lte", liftM snd $ binPrim "lte")
gtePrim = ("gte", liftM snd $ binPrim "gte")
eqPrim = ("eq", liftM snd $ binPrim "eq")
neqPrim = ("neq", liftM snd $ binPrim "neq")

-- | Implements primitive to create data values. The argument
-- specifies the number of values the constructor will take. The
-- function defined here always takes one more argument, which will
-- hold the tag for the value.
mkDataPrim :: UniqueMonad m => Constructor -> Int -> m (ProgM C C)
mkDataPrim tag numArgs = do
  let name = "mkData_" ++ tag
      -- Make the final closure & block for 
      -- executing the "mkDataP" primitive with all the right arguments.
      mkLam bName 0 vs = do
        bLabel <- freshLabel
        let bloConstr = mkFirst (BlockEntry bName bLabel vs) <*>
              mkLast (Done bName bLabel (ConstrM tag vs))
        return (bLabel, bloConstr)
      mkLam cName n vs = do
        cLabel <- freshLabel
        let arg = "t" ++ show (length vs + 1)
            capt = vs ++ [arg]
            nextName = "Constr_" ++ tag ++ "_" ++ show (n - 1)
        (nextLabel, prog) <- mkLam nextName (n - 1) capt
        let cloConstr = mkFirst (CloEntry cName cLabel vs arg) <*>
                        mkLast (Done cName cLabel (if n == 1 
                                                    then Goto (nextName, nextLabel) capt
                                                    else Closure (nextName, nextLabel) capt))
        return (cLabel, cloConstr |*><*| prog)
  (_, p) <- mkLam name numArgs []
  return p

monadic :: UniqueMonad m => (Name -> m (Dest, ProgM C C)) -> Name -> m (Dest, ProgM C C)
monadic rest name  = do
  thunkLabel <- freshLabel
  (dest, prog) <- rest (name ++ "Thunk")
  let thunkBody = mkFirst (BlockEntry name thunkLabel []) <*>
                  mkLast (Done name thunkLabel (Thunk dest []))
  return ((name, thunkLabel), thunkBody |*><*| prog)
  
unaryPrim :: UniqueMonad m => Name -> m (Dest, ProgM C C)
unaryPrim name = do
  bodyLabel <- freshLabel
  c1Label <- freshLabel
  let bodyName = name ++ "Body" 
      body = mkFirst (BlockEntry bodyName bodyLabel ["a"]) <*>
             mkLast (Done bodyName bodyLabel $ Prim name ["a"])
      c1 = mkFirst (CloEntry name c1Label [] "a") <*>
           mkLast (Done name c1Label $ Thunk (bodyName, bodyLabel) ["a"])
  return ((name, c1Label), c1 |*><*| body)
                   
binPrim :: UniqueMonad m => Name -> m (Dest, ProgM C C)
binPrim name = do
  bodyLabel <- freshLabel
  c2Label <- freshLabel
  c1Label <- freshLabel
  let bodyName = name ++ "Body" 
      body = mkFirst (BlockEntry bodyName bodyLabel ["a", "b"]) <*>
             mkLast (Done bodyName bodyLabel $ Prim name ["a", "b"])
      c2Name = name ++ "Clo2"
      c2 = mkFirst (CloEntry c2Name c2Label ["a"] "b") <*>
           mkLast (Done c2Name c2Label $ Goto (bodyName, bodyLabel) ["a", "b"])
      c1 = mkFirst (CloEntry name c1Label [] "a") <*>
           mkLast (Done name c1Label $ Closure (c2Name, c2Label) ["a"])
  return ((name, c1Label), c1 |*><*| c2 |*><*| body)

-- | Doesn't carry any useful information,
-- used by rewriters that calculate no
-- new facts.
type EmptyFact = ()

-- | A no-op transfer function. Used by rewriters that
-- don't gather any new facts.
noOpTrans :: StmtM e x -> Fact x EmptyFact -> EmptyFact
noOpTrans _ _ = ()

-- | Lattice with only one element and no changes.
emptyLattice :: DataflowLattice EmptyFact
emptyLattice = DataflowLattice { fact_name = "Empty fact"
                               , fact_bot = ()
                               , fact_join = \ _ _ _ -> (NoChange, ()) }

