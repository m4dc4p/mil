module Foldr2

where

import Prelude

data List a = Cons a (List a) | Nil
data Nat = S Nat | Z

foldr :: (a -> b -> b) -> b -> List a -> b
foldr f b Nil = b
foldr f b (Cons a as) = f a (foldr f b as)

map :: (a -> b) -> List a -> List b
map f Nil = Nil
map f (Cons a as) = Cons (f a) (map f as)

comp :: (b -> c) -> (a -> b) -> a -> c
comp f g x = f (g x)

add :: Nat -> Nat -> Nat
add Z s = s
add (S n) s = S (add n s)

sum :: List Nat -> Nat
sum = foldr add Z

concat :: List a -> List a -> List a
concat (Cons a as) bs = Cons a (concat as bs)
concat Nil bs = bs

list2 rest = concat (Cons Z (Cons Z Nil)) rest
list4 rest = concat (list2 (list2 Nil)) rest
list8 rest = concat (list4 (list4 Nil)) rest

-- Produce a list of length 16 and determine its
-- length.
main = 
    let ones _ = (S Z)
    in (sum `comp` map ones) (list8 (list8 Nil))

