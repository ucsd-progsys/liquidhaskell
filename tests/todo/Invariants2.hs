module Invariants where

{-@ measure sum :: [Int] -> Nat
    sum()     = 0
    sum(x:xs) = x + (sum xs)
  @-}


{-@ good :: xs:[Int] -> {v:[Int] | (sum xs) >= 0} @-}
good :: [Int] -> [Int]
good x = x
