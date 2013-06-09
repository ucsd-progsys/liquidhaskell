-- Compare with tests/pos/StrictPair1.hs

module SPair (poo) where

import Language.Haskell.Liquid.Prelude (liquidAssert)

{-@ measure tsnd :: (a, b) -> b 
    tsnd (x, y) = y 
  @-} 

{-@ type Foo  a = ((a, Int), Int)<{\z v -> v <= (tsnd z)}> @-}

{-@ poo :: (Foo a) -> () @-}
poo     :: ((a, Int), Int) -> ()
poo ((x, n), m) = liquidAssert (m <= n) () 
