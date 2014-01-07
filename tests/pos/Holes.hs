module Holes where

{-@ foo :: x:_ -> y:{Int | y > 0} -> _ @-}
foo :: Int -> Int -> Int
foo x y = x

zero = foo 0 1


{-@ myId :: x:_ -> a -> _ @-}
myId x y = x


{-@ bar :: {v:[{v0:Int | v0 > 0}] | _ } @-}
bar :: [Int]
bar = [1]
