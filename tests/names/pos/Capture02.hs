module Capture02 where

-- LH issue #1146 

-- tag: rebind 

{-@ exactly :: x:Int -> { n:Int | n = x } @-}
exactly :: Int -> Int 
exactly x = x 

{-@ incr :: n:Int -> {v:_ | v = n + 1 } @-}
incr :: Int -> Int
incr n = exactly (n + 1)

main :: IO ()
main = pure ()
