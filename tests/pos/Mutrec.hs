module Mutrec () where

{-@ isEven :: n:Nat -> Bool / [n, 0] @-}
isEven :: Int -> Bool
isEven 0 = True
isEven n = isOdd (n-1)

{-@ isOdd :: n:Nat -> Bool / [n, 1] @-}
isOdd :: Int -> Bool
isOdd  n = not $ isEven n


{- decrease isEven 1 2 -}
{- decrease isOdd 1 2  -}
