module Foldr
-- Demonstrates definition of foldr. 
where

import Prelude

data List a = Cons a (List a) | Nil
data A = A 

foldr :: (a -> b -> b) -> b -> List a -> b
foldr f b Nil = b
foldr f b (Cons a as) = f a (foldr f b as)

main = foldr (\a b -> b) Nil  (Cons A (Cons A Nil))

