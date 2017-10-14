module Recursion where


{-@ total :: Nat -> Nat @-}
total :: Int -> Int 
total 0 = 0
total n = 1 + total (n-1)

