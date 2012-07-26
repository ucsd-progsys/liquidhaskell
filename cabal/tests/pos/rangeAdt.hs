module Range where

import Language.Haskell.Liquid.Prelude

data L a = Nil | Con a (L a)

range :: Int -> Int -> L Int
range i j  
  | i < j  = i `Con` (range (i + 1) j)
  | otherwise = Nil  

mapL f Nil        = Nil
mapL f (Con x xs) = (f x) `Con` (mapL f xs)  

foldL f b Nil        = b
foldL f b (Con x xs) = foldL f (f b x) xs

sumTo = foldL plus 0 . range 0

n = choose 0 
m = choose 1

prop_rng1 = mapL (liquidAssert . (0 <=)) $ range 0 n
prop_rng2 = mapL (liquidAssert . (n <=)) $ range n 100
prop_rng3 = mapL (liquidAssert . (n <=)) $ range n m
prop_rng4 = mapL (liquidAssert . (<= m)) $ range n m 
prop_rng5 = liquidAssert (0 <= sumTo n)

