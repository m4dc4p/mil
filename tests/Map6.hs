module Map6

-- Testing locally defined recursive functions

where

import Prelude

data Val = A | B | C
data List a         = Nil | Cons a (List a)

main = 
    let map f (Cons e es) = Cons (f e) (map f es)
        map f Nil = Nil
        const a b = a
    in map (const C)  (Cons A (Cons B Nil))
