module HornApp where

inc :: Int -> Int
inc x = x + 1 

foo :: Int -> Int
foo x = inc x

{-@ relational foo ~ foo :: x1:_ -> _ ~ x2:_ -> _ ~~ x1 < x2 => r1 x1 < r2 x2 @-}
