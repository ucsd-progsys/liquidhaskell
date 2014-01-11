module Even () where

{-@ isEven, isOdd :: Nat -> Bool @-}
isEven :: Int -> Bool
isEven 0 = True
isEven n = isOdd  $ n

isOdd  0 = False
isOdd  m = isEven $ m - 1
