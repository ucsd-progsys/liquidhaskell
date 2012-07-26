module Cmp where

import Language.Haskell.Liquid.Prelude

foo x y
 = case compare x y of 
    EQ -> liquidAssert (x == y)
    LT -> liquidAssert (x < y)
    GT -> liquidAssert (x > y)

prop = foo n m 
  where n = choose 0
        m = choose 1
