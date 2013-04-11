module Bad where

import Language.Haskell.Liquid.Prelude

bad []     = []
bad (x:xs) = liquidAssert (x == 100) x : bad xs

decr :: Int -> [Int]
decr n = n : decr (n-1)

prop = bad $ decr 0
