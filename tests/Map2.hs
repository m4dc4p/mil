module Map2 where

-- Testing locally defined functions

import Prelude

data List a         = Nil | Cons a (List a)
data Val = A | B | C

map f (Cons e es) = Cons (f e) (map f es)
map f Nil = Nil

const a b = a

main = 
    let anticonst a b = b -- acts like id
    in map (anticonst A) (Cons B (Cons C Nil))