module Fixme where

abs :: Int -> Int
abs x = if x < 0 then -x else x

{-@ relational abs ~ abs :: x1:Int -> Int ~ x2:Int -> Int
                         ~~ x1 < x2 && x2 < 0 => r1 x1 < r2 x2 @-}
