module Cmp () where

import Language.Haskell.Liquid.Prelude

foo x y
 = case compare x y of 
    EQ -> liquidAssertB (x == y)
    LT -> liquidAssertB (x < y)
    GT -> liquidAssertB (x > y)

prop = foo n m 
  where n = choose 0
        m = choose 1
