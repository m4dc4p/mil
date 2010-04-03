
module Simple where

import Prelude

data List a         = Nil | Cons a (List a)

cons e es = Cons e es
nil = Nil

main = cons nil (cons nil nil)