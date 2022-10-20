module Fixme where

data N = Z | S N

{-@ fib :: N -> { v:Int | v >= 1 } @-}
fib :: N -> Int
fib = let f = \l -> case l of 
            Z           -> 1
            (S Z      ) -> 1
            (S m@(S n)) -> fib n + fib m
        in f

{-@ reflect leq @-}
leq :: N -> N -> Bool
leq Z     _     = True
leq _     Z     = False
leq (S n) (S m) = leq n m

{-@ relational fib ~ fib :: n:_ -> _ ~ m:_ -> _ 
                         | Fixme.leq n m => r1 n <= r2 m @-}



