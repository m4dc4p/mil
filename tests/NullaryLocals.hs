module NullaryLocals

where

-- Demonstrates that locally defined,  zero argument
-- functions are compiled correctly.

import Prelude

data Foo = Foo

main = 
    let x = let x a = Foo
            in x 
        h a = x a
    in h Foo
