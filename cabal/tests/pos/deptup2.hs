module Deptup where

import Language.Haskell.Liquid.Prelude

--myabs x    = if x > 0 then x else (0 - x)

incr x      = x + 1

baz x       = (x, incr x)

bazList  xs = map baz xs

prop_baz xs = map (\(x,y) -> assert (x <= y)) $ bazList xs 
