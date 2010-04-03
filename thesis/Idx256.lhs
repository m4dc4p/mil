> module Idx256 

> where

> dec :: Idx256 -> Maybe Idx256
> dec i = if i > 0 
>         then Just (i - 1)
>         else Nothing

With dec defined as above, what is to prevent us
from returning an index with a negative value? How
can types prevent a dec like this:

> dec2 i = if i > 0
>          then Just (i - (i + 1))
>          else Nothing

> safeDec :: Int -> Int -> Maybe Int
> safeDec idx amt 
>         | idx >= amt = Just (idx - amt)
>         | otherwise = Nothing

> newtype Idx256 = Idx256 Int

> cond :: Idx256 -> (Idx256 -> Idx256) -> Maybe Idx256
> cond (Idx256 i) f 
>      | i > 0 = Just (f (Idx256 i))
>      | otherwise = Nothing

> safeMinus (Idx256 i) = Idx256 (i - 1)

