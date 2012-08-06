module Top where

import Prelude

data Nat = S Nat | Z

_TOP Z s = s
_TOP (S n) s = S (_TOP n s)


main = _TOP Z (S Z)