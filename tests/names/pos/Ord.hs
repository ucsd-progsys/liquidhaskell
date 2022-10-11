module Ord where

{-@ bigger :: x:_ -> y:_ -> {v:_ | v >= x && v >= y} @-}
bigger :: (Ord a) => a -> a -> a 
bigger x y | x `compare` y == GT = x 
           | otherwise           = y
