> {-# LANGUAGE GADTs #-}
> -- Implements optimization to
> -- trim bind/return pairs from the
> -- end of MIL blocks.
> module TrimTail

> where

> import Compiler.Hoopl

> import Util
> import MIL

This is a backwards analysis. We start at the end of a block and, when
it is a return, we determine if that value has two properties:

  * It is not a parameter (i.e., bound locally)
  * It is not used before being bound.

In other words, we determine if the variable is used by any other
statement besides the final "return" while it is live. If not, we know
we can safely eliminate the binding and rewrite the return with the
original tail from the binding.

Our fact is then two pieces of information:

  * The variable is used in a return.
  * The variable is not used anywhere else before being bound.

> type TrimFact = Maybe (Name, Maybe TailM)

Our transfer function has a couple of cases:

  return v ==> Add v to facts.
  bind v t ==> Associate t with v; mark it.
  bind x t, where v appears in t and v is not "marked" ==> Delete v from 
    our facts.

In the second case, we "mark" v to indicate we found its binding and
there was no intervening use. It's possible that v is boudn multiple
times in the same block; we could miss the opportunity to rewrite the
final binding of v due to earlier bindings.

> transferTrim :: BwdTransfer StmtM TrimFact
> transferTrim = mkBTransfer bw
>   where
>     bw :: StmtM e x -> Fact x TrimFact -> TrimFact
>     bw (Done (Return n)) f = Just (n, Nothing)
>     bw (Bind _ _) f@(Just (_, Just _)) = f -- We've already marked our fact, pass it along.
>     bw (Bind v t) f@(Just (v', Nothing))
>       | v == v' = Just (v, Just t) -- "mark" that v' is a valid fact; capture the tail.
>       | t `uses` v' = Nothing -- Remove our fact if it is used in a tail.
>       | otherwise = f -- no effect on our fact, just pass it along.
>     bw (CaseM _ _) _ = Nothing -- Not a valid tail to trim
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

Marking can also copy t to the facts so we can use to rewrite.

Our rewrite function will replace the final return with the tail found
in the facts. It will then eliminate the binding of v by traversing the entire
block backwards and removing the first possible binding.




  

