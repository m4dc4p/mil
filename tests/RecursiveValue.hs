
module RecursiveValue where

import Prelude

data Nat = Z | S Nat

main = 
    let f = S g
        g = S (S f) 
        h (S (S n)) = Z
        h (S n) = (S Z)
    in h g