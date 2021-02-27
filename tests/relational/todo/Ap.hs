module Fixme where

ap :: (Int -> Int) -> Int -> Int
ap f x = f x

{-@ relational ap ~ ap :: f1:_ -> xs1:_ -> _ ~ f2:_ -> xs2:_ -> _ 
                       ~~ f1 == f2 => xs1 == xs2 => r1 f1 xs1 == r2 f2 xs2 @-}
