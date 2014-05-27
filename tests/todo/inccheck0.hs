{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}

module Test0 () where

{-@ decr :: x:Int -> {v:Int | v < x} @-}
decr :: Int -> Int
decr xo = xo - 100

{-@ plus :: x:Int -> y:Int -> {v:Int | v = x + y} @-}
plus :: Int -> Int -> Int
plus x yo = x + yo

{-@ goo :: Int -> Nat @-}
goo :: Int -> Int
goo x = x +  1

{-@ incr :: x:Int -> {v:Int | v > x} @-}
incr :: Int -> Int
incr xoo = xoo  `plus` zaa
  where
     zaa = a00 - b00
     a00 = 300
     b00 = 2

{-@ jog :: x:Int -> {v:Int | v = x} @-}
jog  :: Int -> Int
jog x = x `plus` z
  where 
    z = a - b
    a = 2
    b = 2

{-@ ping, pong :: n:Int -> {v:Int | v > n} @-}
ping, pong :: Int -> Int
ping 0 = 1
ping n = 1 `plus` pong (n-1)

pong 0 = 1 
pong n = 1 `plus` ping (n-1)
