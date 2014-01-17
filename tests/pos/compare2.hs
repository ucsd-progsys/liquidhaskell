module Cmp () where

import Language.Haskell.Liquid.Prelude

foo x y
 | compare x y == EQ = liquidAssertB (x == y)
 | otherwise         = liquidAssertB (True)

prop = foo n m 
  where n = choose 0
        m = choose 1
