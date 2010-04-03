> module Dec 

> where

> import Idx

> dec :: Idx n -> Maybe (Idx n)
> dec idx = runOp (\i -> i - 1) idx

