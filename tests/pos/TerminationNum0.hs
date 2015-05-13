module Fixme where

{-@fak2 :: (Ord a, Eq a, Num a) => {x: a | x >= 0} -> a @-}
fak2 :: (Ord a, Eq a, Num a) => a -> a
fak2 0 = 1
fak2 x = x * fak2 (x - 1)


{-@ fak :: {x: Int | x >= 0} -> a -> Int @-}
fak :: (Ord a, Eq a, Num a) => Int -> a -> Int 
fak 0 _ = 1
fak x y = fak (x - 1) y


{-@ fak1 :: {x: Int | x >= 0} -> a -> Int @-}
fak1 :: (Num a) => Int -> a -> Int 
fak1 0 _ = 1
fak1 x y = fak1 (x - 1) y