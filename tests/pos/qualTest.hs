module QT () where

-- this test demonstrates the inclusion of qualifiers in source files

import Language.Haskell.Liquid.Prelude (liquidAssert)

{-@ qualif Plus100(v:Int, a:Int): (v = a + 100) @-}
 
incr :: Int -> Int
incr x = x + 100

prop = liquidAssert (y == 100) y
  where 
    y  = incr 0 
