module Comp

-- Testing recursive functions

where

import Prelude

data Val = A

comp f g x = f (g x)
id x = x

main = (id `comp` id) A