module Gradual where

{-@ LIQUID "--gradual" @-}
{-@ LIQUID "--eliminate=none" @-}

{-@ unsafe :: {v:Int | ?? } -> Int  -> (Int, Int) @-}
unsafe :: Int -> Int -> (Int, Int)
unsafe _ x = (bar1 x, bar2 x)


{-@ bar1 :: {v:Int | v < 0} -> Int @-}
bar1 :: Int -> Int 
bar1 x = x 

{-@ bar2 :: {v:Int | v = 0} -> Int @-}
bar2 :: Int -> Int 
bar2 x = x