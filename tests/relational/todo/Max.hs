module Fixme where

max :: Int -> Int -> Int 
max a b = if a < b then b else a

{-@ relational max ~ max :: a1:_ -> b1: _ -> _ ~ a2:_ -> b2: _ -> _ 
                         ~~ true => a1 < b1 && a2 < b2 && b1 < b2 => r1 a1 b1 < r2 a2 b2 @-}



