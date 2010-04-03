module Even where

import Prelude

data Nat = Z | S Nat
data Bool = True | False

even Z = True
even (S n) = odd n

odd Z = False
odd (S n) = even n

main = even (S (S Z))
