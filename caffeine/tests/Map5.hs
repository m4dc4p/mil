module Map5 (main) where

-- Testing that locally defined functions
-- and module functions are correctly distinguished, even
-- when top-level functions are not exported.

import Prelude

data Val = A | B | C
data List a         = Nil | Cons a (List a)

map f (Cons e es) = Cons (f e) (map f es)
map f Nil = Nil

const a b = a

main = 
    let const a b = b -- acts like id
    in map (const A) (Cons B (Cons C Nil))