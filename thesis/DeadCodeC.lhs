%if False

> {-# LANGUAGE GADTs, RankNTypes #-}

%endif
%if includeAll

> import Data.List (nub)
> import Data.Set (Set, union, unions, (\\)
>                  , singleton, delete, member)
> import qualified Data.Set as Set
> import Compiler.Hoopl
> import Text.PrettyPrint

%endif
%if includeAst || includeAll

> data CStmt e x where
>   Entry   :: Label -> CStmt C O
>   Assign  :: Var -> CExpr -> CStmt O O
>   Call    :: Var -> [CExpr] -> CStmt O O
>   Return  :: CStmt O C
>
> data CExpr = 
>     Const Int 
>   | Add CExpr CExpr 
>   | Var Var 
>   | String String
>
> type Var = String

%endif
%if nonLocalInst || includeAll

> instance NonLocal CStmt where
>   entryLabel (Entry l)  = l
>   successors Return     = []

%endif
%if buildFoo || includeAll

> example    :: Label -> Graph CStmt C C
> example l  = mkFirst (Entry l) <*> 
>       mkMiddle (Assign "c" (Const 4)) <*>
>       mkMiddle (Assign "a" (Add (Var "c") (Const 1))) <*>
>       mkMiddle (Call "printf" [String "%d", Var "c"]) <*>
>       mkMiddle (Assign "a" (Add (Var "c") (Const 2))) <*>
>       mkLast Return

%endif
%if latticeDef || includeAll

> type Vars = Set Var
>
> meet :: Label -> OldFact Vars -> NewFact Vars -> (ChangeFlag, Vars)
> meet _ (OldFact old) (NewFact new) = (changeIf (old /= new), old `union` new)
>
> lattice :: DataflowLattice Vars
> lattice = DataflowLattice { 
>       fact_name  = "Liveness"
>     , fact_bot   = Set.empty
>     , fact_join  = meet }

%endif
%if includeLiveness || includeAll

> liveness :: BwdTransfer CStmt Vars
> liveness = mkBTransfer transfer
>   where 
>     transfer :: forall e x. CStmt e x -> Fact x Vars -> Vars 
>     transfer (Entry _) f = f
>     transfer (Assign var expr) facts = (var `delete` facts) `union` (uses expr) 
>     transfer (Call _ exprs) facts = facts `union` unions (map uses exprs) 
>     transfer Return _ = Set.empty 
>     
>     uses :: CExpr -> Set Var 
>     uses (Add e1 e2) = uses e1 `union` uses e2
>     uses (Var v) = singleton v
>     uses _ = Set.empty

%endif

%if includeRewrite

> eliminate :: FuelMonad m => BwdRewrite m CStmt Vars
> eliminate = mkBRewrite rewrite
>   where
>     rewrite :: FuelMonad m => forall e x. CStmt e x 
>                -> Fact x Vars -> m (Maybe (Graph CStmt e x))
>     rewrite (Entry _) _ = return Nothing
>     rewrite (Assign var exprs) live = return $
>       if not (var `member` live)
>        then Just emptyGraph
>        else Nothing
>     rewrite (Call _ _) _ = return Nothing
>     rewrite Return _ = return Nothing

%endif
%if includeDeadCode || includeAll

> deadCode :: Graph CStmt C C -> Graph CStmt C C
> deadCode program = runSimpleUniqueMonad $ runWithFuel infiniteFuel $ opt
>   where
>     opt :: CheckingFuelMonad SimpleUniqueMonad (Graph CStmt C C)
>     opt = do
>       (program', _, _) <-  analyzeAndRewriteBwd pass (JustC entryPoints) program 
>                            facts
>       return program' 
>
>     pass = BwdPass {  bp_lattice = lattice, bp_transfer = liveness
>                       , bp_rewrite = eliminate }
>
>     entryPoints = case program of 
>       (GMany _ blocks _) -> map (entry . blockToNodeList') (mapElems blocks)
>
>     entry :: (MaybeC e (CStmt C O), [CStmt O O], MaybeC x (CStmt O C)) 
>              -> Label
>     entry (JustC (Entry l), _, _) = l
>
>     facts :: FactBase Vars
>     facts = mkFactBase lattice (zip entryPoints (repeat Set.empty))

%endif
%if includeAll 

> printProgram :: Graph CStmt C C -> Doc
> printProgram (GMany _ blocks _) = 
>     hcat (map (printBlock . blockToNodeList') $ mapElems blocks)
>   where
>     printBlock :: (MaybeC e (CStmt C O)
>                    , [CStmt O O]
>                    , MaybeC x (CStmt O C)) -> Doc
>     printBlock (JustC entry, mids, JustC last) = 
>       hang (printStmt entry) 2 
>            (vcat (map printStmt mids)) $+$
>       printStmt last

>     printStmt :: forall e x. CStmt e x -> Doc
>     printStmt (Entry _) = text "void example()" <+> lbrace
>     printStmt (Assign v expr) = 
>       text v <+> equals <+> printExpr expr <> semi
>     printStmt (Call fun exprs) = 
>       text fun <> 
>       parens (hcat $ punctuate comma $ map printExpr exprs) <> 
>       semi
>     printStmt Return = rbrace

>     printExpr :: CExpr -> Doc
>     printExpr (Const i) = text (show i)
>     printExpr (Add e1 e2) = printExpr e1 <+> text "+" <+> printExpr e2
>     printExpr (Var v) = text v
>     printExpr (String s) = doubleQuotes (text s)

> main = do 
>   let prog = runSimpleUniqueMonad $ do
>         label <- freshLabel
>         return (example label)
>
>   putStrLn $ "Original Program"
>   putStrLn $ "----------------"
>   putStrLn $ render (printProgram prog)
>
>   putStrLn $ "Optimized Program"
>   putStrLn $ "-----------------"
>   putStrLn $ render (printProgram (deadCode prog))

%endif