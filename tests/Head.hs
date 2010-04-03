module Head where

import Prelude
import Error

data List a         = Nil | Cons a (List a)

-- Head with incomplete pattern match
head (Cons x xs) = x
head _ = error (undefined)

