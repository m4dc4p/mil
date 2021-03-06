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

type ProgM = Graph Stmt
type Dest = (Name, Label)
type Env = [Name]

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

data Stmt e x where
  -- | Entry point to a block.
  BlockEntry :: Name -- Name of the block
    -> Label    -- Label of the entry point.
    -> [Name] -- arguments
    -> Stmt C O

  -- | Entry point to a closure-capturing block.
  CloEntry :: Name -- Name of the block
    -> Label    -- Label of the entry point.
    -> [Name]   -- Variables in closure
    -> Name     -- argument
    -> Stmt C O
  
  Bind :: Name      -- Name of variable that will be bound.
    -> Tail    -- Expression that computes the value we want.
    -> Stmt O O    -- Open/open since bind does not end an expression
  
  Case :: Name      -- Variable to inspect
    -> [Alt Tail] -- Case arms
    -> Stmt O C
      
  Done :: Name -- ^ Name of this block
    -> Label -- ^ Label of this block
    -> Tail  -- Finish a block.
    -> Stmt O C

-- | Tail concludes a list of statements. Each block ends with a
-- Tail except when Case ends the blocks.
data Tail = Return Name 
  | Enter -- ^ Enter a closure.
    Name  -- ^ Variable holding the closure.
    Name  -- ^ Argument to the function.
  | Closure -- ^ Create a closure.
    Dest    -- ^ Label for the function held by the closure.
    [Name]  -- ^ List of captured free variables.
  | Goto   -- ^ Jump to a block.
    Dest   -- ^ Address of the block
    [Name] -- ^ Arguments/live variables used in the block.
  | Constr     -- ^ Create a data value.
    Constructor -- ^ Constructor name.
    [Name]      -- ^ Only variables allowed as arguments to
                -- constructor.
  | Thunk  -- ^ Monadic thunk - suspended computation.
    Dest   -- ^ Label of the computation's body.
    [Name] -- ^ Free variables in the body.
  | Invoke  -- ^ Execute a monadic computation.
    Name  -- ^ Variable holding the thunk
  | Prim    -- ^ Execute a primitive block 
    Name    -- ^ Name of the primitive
    [Name]  -- ^ Arguments to the primitive
  | LitM    -- ^ Numeric value
    Integer 
  deriving (Eq, Ord, Show)

-- Pretty printing programs
printStmtM :: Stmt e x -> Doc
printStmtM (Bind n b) = text n <+> text "<-" <+> nest 2 (printTailM b)
printStmtM (BlockEntry f l args) = text f <+> 
                                  parens (commaSep text args) <> text ":" 
printStmtM (CloEntry f l clos arg) = text f <+> braces (commaSep text clos) 
                                     <+> text arg <> text ":" 
printStmtM (Case v alts) = hang (text "case" <+> text v <+> text "of") 2 (vcat' $ map printAlt alts)
  where
    printAlt (Alt cons vs tailM) = text cons <+> hsep (texts vs) <+> text "->" <+> printTailM tailM
printStmtM (Done _ _ t) = printTailM t

printTailM :: Tail -> Doc
printTailM (Return n) = text "return" <+> text n
printTailM (Enter f a) = text f <+> text "@" <+> text a
printTailM (Closure dest vs) = printDest dest <+> braces (commaSep text vs)
printTailM (Goto dest vs) = printDest dest <> parens (commaSep text vs)
printTailM (Constr cons vs) = text cons <+> (hsep $ texts vs)
printTailM (Thunk dest vs) = printDest dest <+> brackets (commaSep text vs)
printTailM (Invoke v) = text "invoke" <+> text v
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

instance NonLocal Stmt where
  entryLabel (BlockEntry _ l _) = l
  entryLabel (CloEntry _ l _ _) = l
  successors (Case _ alts) = [l | (Alt _ _ (Goto (_, l) _)) <- alts]
  successors (Done _ _ (Goto (_, l) _)) = [l]
  successors _ = []

tailDest :: Tail -> [Dest]
tailDest (Closure dest _) = [dest]
tailDest (Thunk dest _) = [dest]
tailDest (Goto dest _) = [dest]
tailDest _ = []

-- Utility functions

-- | Get all the labels at entry points in 
-- the program.
entryPoints :: ProgM C C -> [(Label, Stmt C O)]
entryPoints (GMany _ blocks _) = map getEntryLabel (mapElems blocks)

-- | Get all entry labels in a program.
entryLabels :: ProgM C C -> [Label]
entryLabels = map fst . entryPoints 

-- | Entry label of a block, pllus the entry instruction.
getEntryLabel :: Block Stmt C x -> (Label, Stmt C O)
getEntryLabel block = case blockToNodeList' block of
  (JustC e@(BlockEntry _ l _), _, _) -> (l, e)
  (JustC e@(CloEntry _ l _ _), _, _) -> (l, e)

-- | Find a block with a given label in the propgram
-- and return it paired with it's label and name.
blockOfLabel :: ProgM C C -> Label -> Maybe (Dest, Block Stmt C C)
blockOfLabel body l = case lookupBlock body l of
                  BodyBlock block -> Just (blockToDest block)
                  _ -> Nothing

destOfEntry :: Stmt C O -> Dest
destOfEntry (BlockEntry n l _) = (n, l)
destOfEntry (CloEntry n l _ _) = (n, l)

-- | Constructin destination label for a given block.
blockToDest :: Block Stmt C C -> (Dest, Block Stmt C C)
blockToDest block = (destOfEntry (blockEntry block), block)

-- | Get the first instruction in a block.
blockEntry :: Block Stmt C C -> Stmt C O
blockEntry b = case blockToNodeList' b of
                 (JustC entry, _, _) -> entry


-- | Find destinatino for a given label, if
-- it exists.
labelToDest :: ProgM C C -> Label -> Maybe Dest
labelToDest prog l = maybe Nothing (Just . fst) (blockOfLabel prog l)

-- | Pair all blocks with their destination.    
allBlocks :: ProgM C C -> [(Dest, Block Stmt C C)]
allBlocks (GMany _ blocks _) = map blockToDest (mapElems blocks)

-- | Get the tail of a block. Will exclude
-- the entry instruction (if C C) or the
-- first instruction in the block (O C)
blockTail :: Block Stmt x C -> ProgM O C
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
done :: Monad m => Name -> Label -> Maybe Tail -> m (Maybe (ProgM O C))
done n l = return . maybe Nothing (Just . mkLast . Done n l)

-- | Create a Bind statement if a Tail is given.
bind :: FuelMonad m => Name -> Maybe Tail -> m (Maybe (ProgM O O))
bind v = return . maybe Nothing (Just . mkMiddle . Bind v)

-- | Create a case statement if alts are given.
_case :: FuelMonad m => Name -> (Alt Tail -> Maybe (Alt Tail)) -> [Alt Tail] -> m (Maybe (ProgM O C))
_case v f alts  
  | any isJust alts' = return $ Just $ mkLast $ Case v (zipWith altZip alts alts')
  | otherwise = return $ Nothing
  where
    alts' = map f alts
    altZip _ (Just a) = a
    altZip a _ = a

-- | Retrieve the name associated with a block (entry statemen).
nameOfEntry :: Stmt C O -> Name
nameOfEntry = fst . destOfEntry

-- | Retrieve all variables mentioned in a tail value.
vars :: Tail -> [Name]
vars (Enter f x) = [f, x]
vars (Closure _ vs) = vs
vars (Goto _ vs) = vs
vars (Constr _ vs) = vs
vars (Thunk _ vs) = vs
vars (Invoke v) = [v]
vars (Prim _ vs) = vs
vars _ = []

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
prims = [printPrim
        , returnPrim
        , readCharPrim
        , unsafeWritePrim
        , newArrayPrim
        , plusPrim
        , minusPrim
        , timesPrim
        , divPrim
        , ltPrim
        , gtPrim
        , ltePrim
        , gtePrim
        , eqPrim
        , neqPrim
        , ("Nil", liftM snd $ mkDataPrim "Nil" 0)
        , ("Cons", liftM snd $ mkDataPrim "Cons" 2)
        , ("Nothing", liftM snd $ mkDataPrim "Nothing" 0)
        , ("Just", liftM snd $ mkDataPrim "Just" 1)
        , ("Unit", liftM snd $ mkDataPrim "Unit" 0)
        ] ++ prioSetPrims
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
      ,("False", liftM snd $ mkDataPrim "False" 0)
      ,("True", liftM snd $ mkDataPrim "True" 0)]

printPrim :: UniqueMonad m => (Name, m (ProgM C C))
printPrim = ("print", liftM snd $ mkMonadicPrim "print" 1)

readCharPrim :: UniqueMonad m => (Name, m (ProgM C C))
readCharPrim = ("readChar", liftM snd $ mkMonadicPrim "readChar" 0)

returnPrim :: UniqueMonad m => (Name, m (ProgM C C))
returnPrim = ("return", liftM snd $ mkMonadicPrim "return" 1)

unsafeWritePrim :: UniqueMonad m => (Name, m (ProgM C C))
unsafeWritePrim = ("unsafeWrite", liftM snd $ mkMonadicPrim "unsafeWrite"  3)

newArrayPrim :: UniqueMonad m => (Name, m (ProgM C C))
newArrayPrim = ("newArray_", liftM snd $ mkMonadicPrim "newArray_" 2)

plusPrim, minusPrim, timesPrim, divPrim, ltPrim, gtPrim, ltePrim, gtePrim, eqPrim, neqPrim :: UniqueMonad m => (Name, m (ProgM C C))
plusPrim = ("plus", liftM snd $ mkPrim "plus" 2)
minusPrim = ("minus", liftM snd $ mkPrim "minus" 2)
timesPrim = ("times", liftM snd $ mkPrim "times" 2)
divPrim = ("div", liftM snd $ mkPrim "div" 2)

ltPrim = ("lt", liftM snd $ mkPrim "lt" 2)
gtPrim = ("gt", liftM snd $ mkPrim "gt" 2)
ltePrim = ("lte", liftM snd $ mkPrim "lte" 2)
gtePrim = ("gte", liftM snd $ mkPrim "gte" 2)
eqPrim = ("eq", liftM snd $ mkPrim "eq" 2)
neqPrim = ("neq", liftM snd $ mkPrim "neq" 2)

monadic :: UniqueMonad m => (Name -> m (Dest, ProgM C C)) -> Name -> m (Dest, ProgM C C)
monadic rest name  = do
  thunkLabel <- freshLabel
  (dest, prog) <- rest (name ++ "Thunk")
  let thunkBody = mkFirst (BlockEntry name thunkLabel []) <*>
                  mkLast (Done name thunkLabel (Thunk dest []))
  return ((name, thunkLabel), thunkBody |*><*| prog)

mkDataPrim :: UniqueMonad m => Name -> Int -> m (Dest, ProgM C C)
mkDataPrim tag numArgs 
  | numArgs == 0 = final []
  | otherwise = do
    (next, rest) <- mkIntermediate final tag numArgs [] 
    dest@(n, l) <- newDest tag
    return (dest
           , (mkFirst (BlockEntry n l []) <*>
              mkLast (Done n l $ Closure next [])) |*><*| 
            rest)
  where
    final args = do
      dest1@(n1, l1) <- if(args == []) 
                        then newDest tag
                        else newDest (tag ++ "body")
      return (dest1
             , (mkFirst (BlockEntry n1 l1 args) <*>
                mkLast (Done n1 l1 (Constr tag args))))

mkPrim :: UniqueMonad m => Name -> Int -> m (Dest, ProgM C C)
mkPrim name numArgs 
  | numArgs == 0 = final []
  | otherwise = do
    (next, rest) <- mkIntermediate final name numArgs [] 
    dest@(n, l) <- newDest name
    return (dest
           , (mkFirst (BlockEntry n l []) <*>
              mkLast (Done n l $ Closure next [])) |*><*| 
            rest)
  where
    final args = do
      dest1@(n1, l1) <- if(args == []) 
                        then newDest name
                        else newDest (name ++ "body")
      return (dest1
             , (mkFirst (BlockEntry n1 l1 args) <*>
                mkLast (Done n1 l1 (Prim name args))))

mkMonadicPrim :: UniqueMonad m => Name -> Int -> m (Dest, ProgM C C)
mkMonadicPrim name numArgs 
  | numArgs == 0 = do
      dest1@(n1, l1) <- newDest name
      dest2@(n2, l2) <- newDest (name ++ "body")
      return (dest1
             , (mkFirst (BlockEntry n1 l1 []) <*>
                mkLast (Done n1 l1 (Thunk dest2 []))) |*><*|
              (mkFirst (BlockEntry n2 l2 []) <*>
               mkLast (Done n2 l2 (Prim name []))))
  | otherwise = do
    (next, rest) <- mkIntermediate final name (numArgs - 1) ["a"] 
    dest@(n, l) <- newDest name
    return (dest
           , (mkFirst (BlockEntry n l []) <*>
              mkLast (Done n l $ Closure next [])) |*><*| 
            rest)
  where
    final args = do
      dest1@(n1, l1) <- newDest (name ++ "mon")
      dest2@(n2, l2) <- newDest (name ++ "body")
      return (dest1
             , (mkFirst (BlockEntry n1 l1 args) <*>
                mkLast (Done n1 l1 (Thunk dest2 args))) |*><*|
              (mkFirst (BlockEntry n2 l2 args) <*>
               mkLast (Done n2 l2 (Prim name args))))

mkIntermediate final _ 0 args = final args 
mkIntermediate final name n args = do
  let arg = "a" ++ show n
      args' = args ++ [arg]
  (next, rest) <- mkIntermediate final name (n - 1) args' 
  dest@(dn, dl) <- newDest (name ++ "clo" ++ show n)
  return (dest
         , (mkFirst (CloEntry dn dl args arg) <*>
            mkLast (Done dn dl $ 
                         if n == 1 
                         then Goto next args'
                         else Closure next args')) |*><*| 
          rest)

newDest name = do
  l <- freshLabel
  return (name, l)

nullaryPrim :: UniqueMonad m => Name -> m (Dest, ProgM C C)
nullaryPrim name = do
  bodyLabel <- freshLabel
  let body = mkFirst (BlockEntry name bodyLabel []) <*>
             mkLast (Done name bodyLabel $ Prim name [])
  return ((name, bodyLabel), body)

unaryPrim :: UniqueMonad m => Name -> m (Dest, ProgM C C)
unaryPrim name = do
  bodyLabel <- freshLabel
  c1Label <- freshLabel
  c2Label <- freshLabel
  let bodyName = name ++ "Body" 
      c1Name = name ++ "c1"
      body = mkFirst (BlockEntry bodyName bodyLabel ["a"]) <*>
             mkLast (Done bodyName bodyLabel $ Prim name ["a"])
      c1 = mkFirst (CloEntry c1Name c1Label [] "a") <*>
           mkLast (Done c1Name c1Label $ Thunk (bodyName, bodyLabel) ["a"])
      c2 = mkFirst (BlockEntry name c2Label []) <*>
           mkLast (Done name c2Label $ Closure (c1Name, c1Label) [])
  return ((name, c2Label), c2 |*><*| c1 |*><*| body)
                   
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
noOpTrans :: Stmt e x -> Fact x EmptyFact -> EmptyFact
noOpTrans _ _ = ()

-- | Lattice with only one element and no changes.
emptyLattice :: DataflowLattice EmptyFact
emptyLattice = DataflowLattice { fact_name = "Empty fact"
                               , fact_bot = ()
                               , fact_join = \ _ _ _ -> (NoChange, ()) }

-- | Create a function which maps names NEW names
-- to ORIGINAL names. If a given name does not appear
-- in the new name list, this functoin returns the name
-- unchanged.
--
-- The function assumes the two lists given correspond.
mkRenamer :: Env -- ^ Original names.
          -> Env -- ^ New names.
          -> (Name -> Name) -- ^ A function mapping new to original.
mkRenamer orig new n = 
  let new2orig = Map.fromList (zip new orig)
  in maybe n id (Map.lookup n new2orig)

-- | Rename all variables in the tail value given, using
-- the renaming function provided.
renameTail :: (Name -> Name) -> Tail -> Tail
renameTail r (Return v) = Return (r v)
renameTail r (Enter f x) = Enter (r f) (r x)
renameTail r (Closure dest vs) = Closure dest (map r vs)
renameTail r (Goto dest vs) = Goto dest (map r vs)
renameTail r (Constr c vs) = Constr c (map r vs)
renameTail r (Thunk dest vs) = Thunk dest (map r vs)
renameTail r (Invoke v) = Invoke (r v)
renameTail r (Prim p vs) = Prim p (map r vs)
renameTail r (LitM i) = LitM i

