module Range () where

import Language.Haskell.Liquid.Prelude

range :: Int -> Int -> [Int]
range i j  
  | i `lt` j  = i : (range (i `plus` 1) j)
  | otherwise = []  

sumTo = foldl plus 0 . range 0

n = choose 0 
m = choose 1

prop_rng1 = map (liquidAssertB . (10 `leq`)) $ range 0 n
prop_rng2 = map (liquidAssertB . (n `leq`)) $ range n 100
prop_rng3 = map (liquidAssertB . (n `leq`)) $ range n m
prop_rng4 = map (liquidAssertB . (`leq` m)) $ range n m 
prop_rng5 = liquidAssertB ((sumTo n) `geq` 10)
