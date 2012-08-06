module Prim

-- Attempting to use primitives but compiler support is not available.

where

import Prelude

data Triple a b c = Triple a b c

primitive type Unit :: *
primitive type Char :: *
primitive putStrLn :: String -> Unit
primitive mkS :: a -> String

data List a = Nil | Cons a (List a)
type String = List Char

concat (Cons a as) bs = (Cons a (concat as bs))
concat Nil bs = bs

showTriple (Triple a b c) = concat (mkS "Triple: ") (mkS a) -- ++ " " ++ mkS b ++ " " ++ mkS c
main = putStrLn (showTriple (Triple "a" "b" "c"))
