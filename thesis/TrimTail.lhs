> {-# LANGUAGE GADTs, RankNTypes, TypeFamilies, ScopedTypeVariables #-}
> -- Implements optimization to
> -- trim bind/return pairs from the
> -- end of MIL blocks.
> module TrimTail 

> where

> import Control.Monad.State (StateT, State(..), MonadState(..), evalStateT)
> import Data.Maybe (listToMaybe, fromMaybe)
> import Compiler.Hoopl
> import Debug.Trace

> import Util
> import MIL

This is a backwards analysis. We start at the end of a block and, when
it is a return, we determine if that value has three properties:

  * It is not a parameter (i.e., bound locally)
  * It is not used before being bound.
  * No monadic actions occur in-between "return" and "bind" for the
    variable.

In other words, we determine if the variable is used by any other
statement besides the final "return" while it is live. We also need to
ensure that no monadic action occurs after the original "invoke". In
that case, even though the result is not used, the side-effect of WHEN
it occurs must be preserved. If neither is true, we know we can safely
eliminate the binding and rewrite the return with the original tail
from the binding.

Our fact is three pieces of information:

  * The variable is used in a return.
  * The variable is not used anywhere else after being bound.
  * No intervening monadic action occurs afer the variable is bound and
    before it is returned.

The third piece of information is represented by its absence: we will
not rewrite a block where it is not true. Therefore, we reprent our
fact using a Maybe value. If no variable exists that can be rewritten,
our fact will be Nothing. Otherwise, it will contain a name and a tail
expression. The tail expression will be "filled in" when the transfer
function finds the variable's binding. If the binding is never found,
the variable is a parameter. In that case, the fact reverts to
Nothing.

> type TrimFact = Maybe (Name, Maybe TailM)

The lattice defined for our facts is simple: 

  * Our bottom element is Nothing 
  * Facts from successor blocks do not affect predecessors (i.e., we
    have a trivial meet operator).

> trimTailLattice :: DataflowLattice TrimFact
> trimTailLattice = DataflowLattice { fact_name = "Trim bind/return tails"
>                                   , fact_bot = Nothing
>                                   , fact_join = extend }
>   where
>     extend _ (OldFact o) (NewFact n) = (changeIf (o /= n), n)

Our transfer function has a couple of cases:

  return v ==> Create our fact (Just v, Nothing). We have found a variable.
  bind x m, where m is monadic ==> Set our fact back to Nothing. Sequences of
    monadic action must be preserved. We cannot rewrite if a mondic
    action happens in between "bind v" and "return v".
  bind v t ==> Create our fact (Just v, Just t); this "marks" our fact and we won't delete it.
  bind x t, where v appears in t and v is not "marked" ==> Set our fact to Nothing again;
    the returned variable is used after being bound.
  block/closure entry, where our fact is (Just v, Nothing) ==> Set our fact
    to Nothing again. The returned variable is a parameter (i.e., no binding was
    found in the block).

In the second case, we "mark" v to indicate we found its binding and
there was no intervening use. It's possible that v is boudn multiple
times in the same block; we could miss the opportunity to rewrite the
final binding of v due to earlier bindings.

> trimTransfer :: BwdTransfer StmtM TrimFact
> trimTransfer = mkBTransfer bw
>   where
>     bw :: StmtM e x -> Fact x TrimFact -> TrimFact
>     bw (Done _ _ (Return n)) f = Just (n, Nothing)
>     bw (Bind _ _) f@(Just (_, Just _)) = f -- We've already marked our fact, pass it along.
>     bw (Bind v t) f@(Just (v', Nothing))
>       | v == v' = Just (v, Just t) -- "mark" that v' is a valid fact; capture the tail.
>       | t `uses` v' = Nothing -- Remove our fact if it is used in a tail.
>       | visibleSideEffect t = Nothing -- Remove our fact, some intervening monadic action occurred.
>       | otherwise = f
>     bw (Bind _ _) _ = Nothing 
>     bw (Done _ _ _) f = Nothing
>     bw (CaseM _ _) _ = Nothing -- Not a valid tail to trim
>     bw (CloEntry _ _ _ _) (Just (_, Nothing)) = Nothing -- Can occur if a used variable is a parameter.
>     bw (BlockEntry _ _ _) (Just (_, Nothing)) = Nothing
>     bw (CloEntry _ _ _ _) f = f
>     bw (BlockEntry _ _ _) f = f
>     
>     uses :: TailM -> Name -> Bool
>     uses (Enter f x) v = f == v || x == v
>     uses (Closure _ vs) v = v `elem` vs
>     uses (Goto _ vs) v = v `elem` vs
>     uses (ConstrM _ vs) v = v `elem` vs
>     uses (Thunk _ vs) v = v `elem` vs
>     uses (Run f) v = f == v
>     uses (Prim _ vs) v = v `elem` vs
>     uses _ _ = False
>    
>     visibleSideEffect :: TailM -> Bool
>     visibleSideEffect (Run {}) = True
>     visibleSideEffect _ = False

Our rewrite function will replace the final return with the tail found
in the facts. It will then eliminate the binding of v by traversing
the entire block backwards and removing the first possible binding. A
StateT monad is used to track if we've rewritten anything yet.

> data RewriteOnce s a = RW { unRw :: s -> SimpleUniqueMonad (s, a) }
> 
> rBind :: RewriteOnce s a -> (a -> RewriteOnce s b) -> RewriteOnce s b
> rBind (RW m) f = RW $ \s -> 
>                  let (s', a) = runSimpleUniqueMonad (m s)
>                      (RW m') = f a
>                  in (m' s')

> evalRw :: s -> RewriteOnce s a -> SimpleUniqueMonad a                      
> evalRw s (RW m) = do
>   (_, a) <- m s
>   return a

> instance Monad (RewriteOnce s) where
>   (>>=) = rBind
>   return a = RW $ \s -> return (s, a)

> rCheckpoint :: RewriteOnce s (s, [Unique])
> rCheckpoint = RW $ \s -> do
>               us <- checkpoint
>               return (s, (s, us))
>                     
> rRestart :: (s, [Unique]) -> RewriteOnce s ()
> rRestart (s, us) = RW (\_ -> restart us >> return (s, ()))

> instance CheckpointMonad (RewriteOnce s) where
>   type Checkpoint (RewriteOnce s) = (s, Checkpoint SimpleUniqueMonad)
>   checkpoint = rCheckpoint
>   restart = rRestart

> -- trimRewrite :: BwdRewrite (CheckingFuelMonad (RewriteOnce s)) StmtM TrimFact
> trimRewrite :: BwdRewrite SimpleFuelMonad StmtM Trimmed
> trimRewrite = mkBRewrite rewriter

> rewriter :: FuelMonad m => forall e x. StmtM e x -> Fact x Trimmed -> m (Maybe (ProgM e x))
> rewriter (Bind v t) (ReplaceBind, Just (v', (Just t'))) 
>   | v == v' && t == t' = return $ Just emptyGraph
>   | otherwise = return Nothing
> rewriter (Done n l (Return v)) fs = 
>   case fromMaybe (End, Nothing) (mapLookup l fs) of
>     (ReplaceDone, Just (v', Just t')) -> done n l (Just t')
>     _ -> return Nothing
> rewriter (Bind _ _) fs = return Nothing
> rewriter (Done _ _ _) _ = return Nothing
> rewriter (CaseM _ _) _ = return Nothing
> rewriter (BlockEntry _ _ _) _ = return Nothing
> rewriter (CloEntry _ _ _ _) _ = return Nothing

> type Trimmed = (TrimState, TrimFact)
> data TrimState = Begin | ReplaceDone | ReplaceBind | End
>   deriving (Eq, Show)

> trimmedTransfer :: StmtM e x -> Fact x Trimmed -> Trimmed
> trimmedTransfer (Bind v t) f@(ReplaceBind, Just (v', Just t'))
>   | v == v' && t == t' = (End, Nothing)
>   | otherwise = f
> trimmedTransfer (Bind _ _) f = f
> trimmedTransfer (Done _ l t) fs = 
>   case fromMaybe (Begin, Nothing) (mapLookup l fs) of
>     (Begin, f@(Just (_, Just t')))
>       | t /= t' -> (ReplaceDone, f) -- haven't replaced tail yet
>     (ReplaceDone, f) -> (ReplaceBind, f)
>     (ReplaceBind, f) -> (End, Nothing)
>     _ -> (End, Nothing)
> trimmedTransfer (CaseM _ _) fs = (End, Nothing)
> trimmedTransfer (CloEntry _ _ _ _) f = f
> trimmedTransfer (BlockEntry _ _ _) f = f

> trimmedLattice :: DataflowLattice Trimmed
> trimmedLattice = DataflowLattice { fact_name = "Trimmed bind/return tails"
>                                  , fact_bot = (Begin, Nothing)
>                                  , fact_join = extend }
>   where
>     extend _ (OldFact o) (NewFact n) = (changeIf (o /= n), n)

> -- bwd2 :: BwdPass (CheckingFuelMonad (RewriteOnce s)) StmtM TrimFact                           
> bwd2 :: BwdPass SimpleFuelMonad StmtM Trimmed
> bwd2 = BwdPass { bp_lattice = trimmedLattice 
>                , bp_transfer = mkBTransfer trimmedTransfer
>                , bp_rewrite = trimRewrite }

> trimTail :: ProgM C C -> ProgM C C
> -- trimTail body = runSimpleUniqueMonad $ evalRw True $ runWithFuel infiniteFuel $ do
> trimTail body = runSimple $ do
>     (_, f, _) <- analyzeAndRewriteBwd bwd1 (JustC labels) body initial
>     (body', _, _) <- analyzeAndRewriteBwd bwd2 (JustC labels) body (toTrimmed f)
>     return body'
>   where
>     labels = entryLabels body
>     initial = mkFactBase (bp_lattice bwd1) (zip labels (repeat Nothing))
>     toTrimmed :: FactBase TrimFact -> FactBase Trimmed
>     toTrimmed fs = mapMap (\f -> (Begin, f)) fs
>     bwd1 = BwdPass { bp_lattice = trimTailLattice 
>                   , bp_transfer = trimTransfer 
>                   , bp_rewrite = noBwdRewrite }

