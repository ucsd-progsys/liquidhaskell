module Gradual where

{-@ safe :: {v:Int | ?? } -> (Int, Int) @-}
safe :: Int -> (Int, Int)
safe x = (bar1 x, bar2 x)

{-@ bar1 :: {v:Int | v < 0} -> Int @-}
bar1 :: Int -> Int 
bar1 x = x 

{-@ bar2 :: {v:Int | v = 0} -> Int @-}
bar2 :: Int -> Int 
bar2 x = x