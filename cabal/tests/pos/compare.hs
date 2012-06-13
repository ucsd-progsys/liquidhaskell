module Cmp where

import Language.Haskell.Liquid.Prelude

foo x y
 = case compare x y of 
    EQ -> assert (x == y)
    LT -> assert (x < y)
    GT -> assert (x > y)

prop = foo n m 
  where n = choose 0
        m = choose 1
