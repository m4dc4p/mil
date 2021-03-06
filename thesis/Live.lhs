%if False

> {-# LANGUAGE TypeSynonymInstances, GADTs, RankNTypes
>   , NamedFieldPuns, TypeFamilies, ScopedTypeVariables #-}
> module Live (addLive, LiveFact, deadCode, deadCodePass, findLive)
>
> where 
> 
> import Control.Monad.State (State, execState, modify, gets)
> import Text.PrettyPrint 
> import Data.List (sort, (\\), elemIndex)
> import Data.Maybe (fromMaybe, isJust, catMaybes, fromJust)
> import Data.Map (Map, (!))
> import qualified Data.Map as Map
> import Data.Set (Set)
> import qualified Data.Set as Set

> import Compiler.Hoopl
> 
> import Util
> import MIL
> 
> -- | Annotate block and closure entry 
> -- points with live variables.
> addLive :: [Name] -> ProgM C C -> ProgM C C 
> addLive tops = fst . usingLive addLiveRewriter tops
>     
> -- | Eliminate dead bindings in blocks.  
> deadCode :: ProgM C C -> ProgM C C
> deadCode = fst . usingLive deadRewriter []
> 
> deadCodePass :: FuelMonad m => [Name] -> BwdPass m Stmt LiveFact
> deadCodePass = mkLivePass deadRewriter
>
> -- Determining liveness in Stmt

%endif
%if deadcode 

When eliminating bindings, we need to track the variables that 
are live at any point. Our ``fact'' is then a set of variables:

> type LiveFact = Set Name

%endif
%if False

> mkLivePass :: FuelMonad m => (Set Name -> BwdRewrite m Stmt LiveFact) -- ^ Rewrite to use
>            -> [Name] 
>            -> BwdPass m Stmt LiveFact
> mkLivePass rewriter tops = 
>   BwdPass { bp_lattice = liveLattice (undefined :: Name) "live statements"
>           , bp_transfer = liveTransfer (Set.fromList tops)
>           , bp_rewrite = rewriter (Set.fromList tops) } 

> -- | Used to apply different rewriters which all require 
> -- live variable analysis.
> usingLive :: (forall m. FuelMonad m => Set Name -> BwdRewrite m Stmt LiveFact) -- ^ Rewrite to use
>           -> [Name] -- ^ Top-level variables
>           -> ProgM C C -- ^ Program to rewrite
>           -> (ProgM C C, FactBase LiveFact) -- Results
> usingLive rewriter tops body = runSimple $ do
>       (p, f, _) <- analyzeAndRewriteBwd bwd (JustC (entryLabels body)) body mapEmpty
>       return (p, f)
>   where
>     bwd = mkLivePass rewriter tops
> 
> -- | Initial setup for liveness analysis.
> liveLattice :: Ord a => a -> String -> DataflowLattice (Set a)
> liveLattice _ name = DataflowLattice { fact_name = name
>                               , fact_bot = Set.empty
>                               , fact_join = extend }
>   where
>     extend _ (OldFact old) (NewFact new) = (changeIf (new /= old)
>                                            , new)
> 
> -- | Transfer liveness backwards across nodes.                                         

%endif
%if deadcode

Analyzing each statement means we need to find all variables used and
add them to our set of live variables. The signature |BwdTransfer
Stmt LiveFact| expresses that this is a backwards analysis over our
statements, collecting liveness facts. We can also give a set of
top-level names (|tops|), that ensures we do not see every top-level
primitive and user-defined function as a ``live'' variable. For
dead-code elimination this doesn't have any effect.
\savecolumns

> liveTransfer :: Set Name -> BwdTransfer Stmt LiveFact
> liveTransfer tops = mkBTransfer live
>   where
>     live :: Stmt e x -> Fact x LiveFact -> LiveFact


Our analysis treats each type of statement seperately. Entry labels do
not add any live variables, but they remove live variables which match
their arguments.
\restorecolumns

>     live (BlockEntry n _ args) f = Set.difference (Set.difference f (Set.fromList args)) tops
>     live (CloEntry n _ _ arg) f = Set.delete arg f

A binding will add the variables (|tailVars t|) used and eliminate the bound
variable (|v|). We must elminate variables as they are bound because analysis
proceeds backwards. You cannot use a variable before it has been declared!
\restorecolumns

>     live (Bind v t) f = Set.delete v f  `Set.union` tailVars t 

|Case| and |Done| add variables based on the tails found. |Done| only
needs to consider its tail expression. For |Case|, we need
to take the union of all variables used. 
\restorecolumns

>     live (Case v alts) f = Set.insert v (Set.unions (map (setAlt f) alts))
>     live (Done _ _ t) f = tailVars t

|setAlt| gathers the variables used in each case alternative, and
makes sure to remove any variables bound by pattern matching.
\restorecolumns

>     setAlt :: FactBase LiveFact -> Alt Tail -> Set Name
>     setAlt f (Alt _ ns e) = Set.difference (tailVars e) (Set.fromList ns)

For completeness, we show |tailVars| below. |tailVars| gathers the names used in
each type of tail expression.
\restorecolumns

>     tailVars :: Tail -> Set Name
>     tailVars (Closure _ vs) = Set.fromList vs 
>     tailVars (Goto _ vs) = Set.fromList vs
>     tailVars (Enter v1 v2) = Set.fromList [v1, v2]
>     tailVars (Constr _ vs) = Set.fromList vs
>     tailVars (Return n) = Set.singleton n
>     tailVars (Thunk _ vs) = Set.fromList vs
>     tailVars (Invoke n) = Set.singleton n
>     tailVars (Prim _ vs) = Set.fromList vs
>     tailVars (LitM _) = Set.empty

%endif
%if False

> -- | Retrieve a fact or the empty set
> liveFact :: FactBase LiveFact -> Label -> Set Name
> liveFact f l = fromMaybe Set.empty $ lookupFact l f
> 
> -- | Returns live variables associated with each
> -- label in the program.
> findLive :: [Name] -- ^ Top-level variables
>          -> ProgM C C -- ^ Program to analyze
>          -> FactBase LiveFact -- Results
> findLive tops = snd . usingLive (const noBwdRewrite) tops 
> 
> -- | Adds live variables to Goto and BlockEntry instructions. Not
> -- filled in by the compiler - added in this pass instead.
> addLiveRewriter :: FuelMonad m => Set Name -> BwdRewrite m Stmt LiveFact
> addLiveRewriter tops = mkBRewrite rewrite
>   where
>     rewrite :: FuelMonad m => forall e x. Stmt e x -> Fact x LiveFact -> m (Maybe (ProgM e x))
>     rewrite (Done n l t) f = done n l (rewriteTail f t)
>     rewrite (BlockEntry n l args) live 
>       | Set.difference live tops /= Set.fromList args = blockEntry n l (sort (Set.toList live))
>     rewrite (Case n alts) f = _case n (rewriteAlt f) alts
>     -- Why do I not need to worry about Bind here? What shows I can't have a 
>     -- Goto in the tail?
>     rewrite _ _ = return Nothing
>     
>     rewriteAlt f (Alt c ns t) = maybe Nothing (Just . Alt c ns) (rewriteTail f t)
> 
>     rewriteTail :: FactBase LiveFact -> Tail -> Maybe Tail
>     rewriteTail f (Goto (n, l) vs) = 
>       case l `mapLookup` f of
>         Just vs' 
>           | vs' /= Set.fromList vs -> Just (Goto (n,l) (sort (Set.toList vs')))
>         _ -> Nothing
>     rewriteTail _ _ = Nothing
>     
>     blockEntry :: FuelMonad m => Name -> Label -> [Name] -> m (Maybe (ProgM C O))
>     blockEntry n l args = return $ Just $ mkFirst $ BlockEntry n l args
> 
> -- | From mon5.lhs
> --
> --   Compile-time garbage collection:
> --    Bind v a c           ==> c         if a is an allocator and
> --                                          v doesn't appear in c
> --
> -- deadRewriter implemented similary, where "safe" determines if the
> -- expression on the right of the array can be elminiated safely.
> -- 

%endif
%if deadcode
%{

%% This ensures the "." in the forall statement does not
%% format as composition.

%format . = ".\ "

Our rewriting function does not have much work to do once the transfer
function has completed its work. The type of |deadRewriter| indicates
that we proceed backward over our statements, using liveness
facts. Our actual rewrite function, |rewrite|, has a type which
indicates it will possibly rewrite statements to graphs of the same
shape.
\savecolumns

> deadRewriter :: FuelMonad m => Set Name -> BwdRewrite m Stmt LiveFact
> deadRewriter _ = mkBRewrite rewrite
>   where
>     rewrite :: FuelMonad m => forall e x. Stmt e x 
>                -> Fact x LiveFact 
>                -> m (Maybe (ProgM e x))

%}

The only rewriting the function might do is when a |Bind| statement is
encountered. If the variable bound, |v|, is not live and the tail expression
is safe (i.e., only allocates), then we can eliminate the statement by
returning |Just emptyGraph|. Otherwise, we return |Nothing|, indicating the
statement should not be modified.
\restorecolumns

>     rewrite (Bind v t) f 
>             | safe t && not (v `Set.member` f) = return (Just emptyGraph)
>     rewrite _ _ = return Nothing


For completeness, our |safe| function is below. Instructions that only
allocate are considered safe. We do not consider |Goto| expressions
safe, as the block called may contain a |Invoke| expression. |Prim| and
|Enter| expressions are not safe, as they may have side-effects.

%if False

>     -- Indicates when it is OK to eliminate a tail instruction in a monadic
>     -- expression.

%endif
\restorecolumns

>     safe :: Tail -> Bool
>     safe (Return _) = True
>     safe (Closure _ _) = True
>     safe (Constr _ _) = True
>     safe (Thunk _ _) = True 
>     safe (LitM _) = True
>     safe _ = False

%endif
%if False

> 
> -- | printing live facts
> printLiveFacts :: FactBase LiveFact -> Doc
> printLiveFacts = printFB printFact
>   where
>     printFact :: (Label, Set Name) -> Doc
>     printFact (l, ns) = text (show l) <> text ":" <+> commaSep text (Set.elems ns)

%endif