module Cmp () where

import Language.Haskell.Liquid.Prelude

foo x y
 | compare x y == EQ = liquidAssertB (x == y)
 | compare x y == LT = liquidAssertB (x < y)
 | compare x y == GT = liquidAssertB (x >  y)

prop = foo n m 
  where n = choose 0
        m = choose 1
