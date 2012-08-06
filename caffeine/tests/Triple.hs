module Triple 

where

import Prelude

data Triple a b c = Triple a b c
data V = A | B | C

which A = Triple A A A
which B = Triple B B B

main = which A
