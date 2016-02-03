module Gradual where

{-@ safe1 :: {v:Int | ?? } -> (Int, Int) @-}
safe1 :: Int -> (Int, Int)
safe1 x = (bar1 x, bar2 x)



{-@ safe2 :: {v:Int | ?? } -> Int  -> (Int, Int) @-}
safe2 :: Int -> Int -> (Int, Int)
safe2 _ x = (bar1 x, bar2 x)


{-@ bar1 :: {v:Int | v < 0} -> Int @-}
bar1 :: Int -> Int 
bar1 x = x 

{-@ bar2 :: {v:Int | v = 0} -> Int @-}
bar2 :: Int -> Int 
bar2 x = x