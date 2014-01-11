module Range (single, prop_rng1) where

import Language.Haskell.Liquid.Prelude

mynil  = []

single x = [x] 

range :: Int -> Int -> [Int]
range i j = [i]

prop_rng1 n   = map (liquidAssertB . (0 <=)) $ range 0 n
