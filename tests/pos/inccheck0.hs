module Test0 where

{-@ incr :: x:Int -> {v:Int | v = x} @-}
incr :: Int -> Int
incr x = x + z
  where
     z = a - b
     a = 2
     b = 1

{-@ decr :: x:Int -> {v:Int | v < x} @-}
decr :: Int -> Int
decr x = x - 1

{-@ jog :: x:Int -> {v:Int | v = x} @-}
jog  :: Int -> Int
jog x = x + z
  where 
    z = a - b
    a = 2
    b = 2
