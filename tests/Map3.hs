module Map3 

-- Demonstrates mutually recursive, locally
-- defined functions.

where

data Nat = S Nat | Z
data Bool = True | False

main = 
    let even Z = True
        even (S n) = odd n

        odd Z = False
        odd (S n) = even n
    in odd (S (S Z))
