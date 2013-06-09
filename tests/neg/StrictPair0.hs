-- Compare with tests/neg/StrictPair1.hs

module SPair (poo) where

{-@ measure tsnd :: (a, b) -> b 
    tsnd (x, y) = y 
  @-} 

{-@ type Foo  a = ((a, Int), Int)<{\z v -> v <= (tsnd z)}> @-}

{-@ poo :: a -> Int -> (Foo a) @-}
poo     :: a -> Int -> ((a, Int), Int)
poo x n = ((x, n), m)
  where
    m   = n + 1
