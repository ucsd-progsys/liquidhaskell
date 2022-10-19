{-@ LIQUID "--expect-any-error" @-}
module Fixme where

data N = Z | S N

{-@ fib :: N -> { v:Int | v >= 1 } @-}
fib :: N -> Int
fib Z           = 1
fib (S Z      ) = 1
fib (S m@(S n)) = fib n + fib m

{-@ reflect leq @-}
leq :: N -> N -> Bool
leq Z     _     = True
leq _     Z     = False
leq (S n) (S m) = leq n m

{-@ relational fib ~ fib :: n1:_ -> _ ~ n2:_ -> _ 
                         ~~ Fixme.leq n1 n2 => r1 < r2 @-}



