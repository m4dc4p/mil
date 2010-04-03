module NullaryFuncs

where

-- Demonstrates that top-level, zero argument
-- functions are compiled correctly.

import Prelude

data Foo a = Foo a
data Bar = Bar 
x = let x a = Foo a
    in x 
h a = x a

main = h Bar
