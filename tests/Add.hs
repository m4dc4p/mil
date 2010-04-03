module Add where

import Prelude

data Nat = S Nat | Z

add Z s = s
add (S n) s = S (add n s)


main = add Z (S Z)