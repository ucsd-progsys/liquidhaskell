module Fixme where

{-@ fak2 :: (Ord a, Eq a, Num a) => y:{x: a | x >= 0} -> a /[y]@-}
fak2 :: (Ord a, Eq a, Num a) => a -> a
fak2 0 = 1
fak2 x = x * fak2 (x - 1)