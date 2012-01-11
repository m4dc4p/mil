]%if False

> {-# LANGUAGE GADTs, RankNTypes #-}

%endif
%if includeAll

> import Data.List (nub)
> import Debug.Trace
> import Data.Maybe (fromJust, catMaybes)
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
>   If      :: CExpr -> Label -> Label -> CStmt O C
>   Goto    :: Label -> CStmt O C
>   Dest    :: Label -> CStmt C O
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
>   entryLabel (Dest l)   = l
>   successors Return     = []
>   successors (Goto l)   = [l]
>   successors (If _ tl fl)  = [tl, fl]

%endif
%if buildFoo || includeAll

> example    = do 
>   [entryLabel, leaveLabel, trueLabel, falseLabel] <- sequence $ take 4 $ (repeat freshLabel)
>   let enter  =  mkFirst (Entry entryLabel) <*> 
>         mkMiddle (Assign "c" (Const 4)) <*>
>         mkLast (If (Var "c") trueLabel falseLabel)
>       true   =  mkFirst (Dest trueLabel) <*>
>         mkMiddle (Assign "a" (Add (Var "c") (Const 1))) <*>
>         mkLast (Goto leaveLabel)
>       false  =  mkFirst (Dest falseLabel) <*>
>         mkMiddle (Assign "a" (Add (Var "c") (Const 2))) <*>
>         mkLast (Goto leaveLabel)
>       leave  =  mkFirst (Dest leaveLabel) <*>
>         mkMiddle (Call "printf" [String "%d", Var "c"]) <*>
>         mkMiddle (Assign "a" (Add (Var "c") (Const 3))) <*>
>         mkLast Return
>   return (enter |*><*| true |*><*| false |*><*| leave)

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
>     transfer :: forall e x. CStmt e x -> Fact x Vars -> Vars {-"\label{hoopl_eg_transfer}"-}
>     transfer (Entry _) _ = Set.empty {-"\label{hoopl_eg_transfer_entry}"-}
>     transfer (Dest _) f = f {-"\label{hoopl_eg_transfer_dest}"-}
>     transfer (Assign var expr) facts = (var `delete` facts) `union` (uses expr) {-"\label{hoopl_eg_transfer_assign}"-}
>     transfer (Call _ exprs) facts = facts `union` unions (map uses exprs) {-"\label{hoopl_eg_transfer_call}"-}
>     transfer s@(If testExpr _ _) facts = uses testExpr `union` joinFacts lattice undefined (successorFacts s facts)
>     transfer s@(Goto _) facts = joinFacts lattice undefined (successorFacts s facts)
>     transfer Return _ = Set.empty {-"\label{hoopl_eg_transfer_return}"-}
>     
>     uses :: CExpr -> Set Var {-"\label{hoopl_eg_transfer_uses}"-}
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
>     rewrite (Dest _) _ = return Nothing
>     rewrite (Assign var exprs) live = return $
>       if not (var `member` live)
>        then Just emptyGraph
>        else Nothing
>     rewrite (Call _ _) _ = return Nothing
>     rewrite (If _ tg fg) _ = return Nothing
>     rewrite (Goto _) _ = return Nothing
>     rewrite Return _ = return Nothing

%endif
%if includeDeadCode || includeAll

> deadCode :: Graph CStmt C C -> Graph CStmt C C
> deadCode program = runSimpleUniqueMonad $ runWithFuel infiniteFuel $ do
>       (program', _, _) <- (analyzeAndRewriteBwd 
>                            pass (JustC entryPoints) program facts)
>       return program' :: SimpleFuelMonad (Graph CStmt C C)
>   where
>
>     pass = debugBwdJoins trace (const True)  $ BwdPass { bp_lattice = lattice
>                   , bp_transfer = liveness 
>                   , bp_rewrite = eliminate }
>
>     entryPoints = case program of 
>       (GMany _ blocks _) -> map (entry . blockToNodeList') (mapElems blocks)
>
>     entry :: (MaybeC e (CStmt C O), [CStmt O O], MaybeC x (CStmt O C)) 
>              -> Label
>     entry (JustC (Entry l), _, _) = l
>     entry (JustC (Dest l), _, _) = l
>
>     facts :: FactBase Vars
>     facts = mkFactBase lattice (zip entryPoints (repeat Set.empty))

%endif
%if includeAll 

> printProgram :: Graph CStmt e C -> Doc
> printProgram (GMany NothingO blocks _) = 
>     hcat (map (printBlock . blockToNodeList') $ mapElems blocks)
> printProgram (GMany (JustO entry) _ _) = printBlock (blockToNodeList' entry)
>   
> printBlock :: (MaybeC e (CStmt C O)
>                    , [CStmt O O]
>                    , MaybeC x (CStmt O C)) -> Doc
> printBlock (JustC entry, mids, JustC last) = 
>   hang (printStmt entry) 2 
>        (vcat (map printStmt mids)) $+$
>   printStmt last
> printBlock (NothingC, mids, JustC last) = vcat (map printStmt mids) $+$ 
>   printStmt last

> printStmt :: forall e x. CStmt e x -> Doc
> printStmt (Entry _) = text "void example()" <+> lbrace
> printStmt (Dest _) = empty
> printStmt (Assign v expr) = 
>       text v <+> equals <+> printExpr expr <> semi
> printStmt (Goto _) = empty
> printStmt (Call fun exprs) = 
>       text fun <> 
>       parens (hcat $ punctuate comma $ map printExpr exprs) <> 
>       semi
> printStmt (If testExpr tl fl) =
>       hang (text "if(" <> printExpr testExpr <> text ")" <+> lbrace) 2
>            (text (show tl)) $+$
>       hang (rbrace <+> text "else" <+> lbrace) 2
>            (text (show fl)) $+$
>       rbrace
> printStmt Return = rbrace

> printExpr :: CExpr -> Doc
> printExpr (Const i) = text (show i)
> printExpr (Add e1 e2) = printExpr e1 <+> text "+" <+> printExpr e2
> printExpr (Var v) = text v
> printExpr (String s) = doubleQuotes (text s)

> main = do 
>   let prog = runSimpleUniqueMonad example
>
>   putStrLn $ "Original Program"
>   putStrLn $ "----------------"
>   putStrLn $ render (printProgram prog)
>
>   putStrLn $ "Optimized Program"
>   putStrLn $ "-----------------"
>   putStrLn $ render (printProgram (deadCode prog))

%endif