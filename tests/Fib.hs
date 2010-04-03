module Fib where

import Prelude

data Nat = Z 
         | S Nat

add Z s = s
add (S n) m = S (add n m)

fib Z = S Z
fib (S Z) = S Z
fib (S (S n)) = add (fib (S n)) (fib n)

three = S (S (S Z))
eight = S (S (S (S (S (S (S (S Z)))))))

-- fib 8 = 34
-- fib 3 = 4
main = fib eight