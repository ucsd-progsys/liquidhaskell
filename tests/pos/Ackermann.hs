{--! run liquid with termination -}

module Ackermann where

{-@ ack :: Nat -> Nat -> Nat @-}
{-@ Decrease ack 1 2 @-}
ack :: Int -> Int -> Int
ack m n
    | m == 0          = n + 1
    | m > 0 && n == 0 = ack (m-1) 1
    | m > 0 && n >  0 = ack (m-1) (ack m (n-1))
