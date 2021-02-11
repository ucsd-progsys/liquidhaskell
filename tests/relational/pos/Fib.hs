module Fixme where

data N = Z | S N

fib :: N -> Int
fib Z           = 1
fib (S Z      ) = 1
fib (S m@(S n)) = fib n + fib m

{-@ reflect leq @-}
leq :: N -> N -> Bool
leq Z     _     = True
leq _     Z     = False
leq (S n) (S m) = leq n m

{-@ relational fib ~ fib :: a1:N -> { v:Int | v >= 1 } ~ a2:N -> { v:Int | v >= 1 }
                         ~~ Fixme.leq a1 a2 => r1 a1 <= r2 a2 @-}

