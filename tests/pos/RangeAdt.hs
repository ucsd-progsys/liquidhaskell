module RangeAdt (llen) where

import Language.Haskell.Liquid.Prelude

data L a = Nil | Con a (L a)
{-@ data L [llen] a = Nil | Con { lHd ::a, lTl :: L a } @-}

{-@ measure llen @-}
{-@ llen :: L a -> Nat @-}
llen :: L a -> Int 
llen Nil = 0 
llen (Con _ xs) = 1 + llen xs 

range :: Int -> Int -> L Int
range i j = range' (j-i) i j

range' :: Int -> Int -> Int -> L Int
range' d i j
  | i < j  = i `Con` (range' (d-1) (i + 1) j)
  | otherwise = Nil

mapL f Nil        = Nil
mapL f (Con x xs) = (f x) `Con` (mapL f xs)

foldL f b Nil        = b
foldL f b (Con x xs) = foldL f (f b x) xs

sumTo = foldL plus 0 . range 0

n = choose 0
m = choose 1

prop_rng1 = mapL (liquidAssertB . (0 <=)) $ range 0 n
prop_rng2 = mapL (liquidAssertB . (n <=)) $ range n 100
prop_rng3 = mapL (liquidAssertB . (n <=)) $ range n m
prop_rng4 = mapL (liquidAssertB . (<= m)) $ range n m
prop_rng5 = liquidAssertB (0 <= sumTo n)
