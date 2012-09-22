module Range where

import Language.Haskell.Liquid.Prelude

range :: Int -> Int -> [Int]
range i j  
  | i < j     = i : (range (i + 1) j)
  | otherwise = []  


sumTo = foldl (+) 0 . range 0 

--myfoldl :: (Int -> Int -> Int) -> Int -> [Int] -> Int
myfoldl f z0 xs0 = lgo z0 xs0
             where
                lgo z []     =  z
                lgo z (x:xs) = lgo (f z x) xs
n = choose 0 
m = choose 1

-- prop_rng1 = map (liquidAssertB . (0 <=)) $ range 0 n
-- prop_rng2 = map (liquidAssertB . (n <=)) $ range n 100
-- prop_rng3 = map (liquidAssertB . (n <=)) $ range n m
-- prop_rng4 = map (liquidAssertB . (<= m)) $ range n m 
prop_rng5 = liquidAssertB (0 <= sumTo n)
