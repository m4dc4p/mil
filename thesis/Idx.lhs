> module Idx (runOp, Idx)

> where

> newtype Idx n = Idx Int

> runOp :: (Int -> Int) -> Idx n -> Maybe (Idx n)
> runOp f (Idx i) = 
>     let j = f i
>     in if j > 0
>        then Just (Idx j)
>        else Nothing

