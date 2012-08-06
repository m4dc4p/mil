module Uninterp

-- This program cannot be run by the register machine
-- interpreter. The problem is the recursive call
-- in f. 

where

import Prelude

data X = Y | W X 

main = 
    let f (W ys) = W (f ys) 
    in f (W (W Y))
