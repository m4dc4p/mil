module Map4 

-- Testing mutually recursive functions.

where

import Prelude

data List a         = Nil | Cons a (List a)
data Val = A | B 

m1 f Nil = Nil
m1 f (Cons a b) = Cons (f a) (m2 f b)
m2 f Nil = Nil
m2 f (Cons a b) = Cons (f a) (m1 f b)

main = m1 (\x -> x) (Cons A (Cons B Nil))