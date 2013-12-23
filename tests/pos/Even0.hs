module Even where

{-@ isEven :: n:Nat -> Bool / [n, 0]@-}
{-@ isOdd  :: mmm:Nat -> Bool / [mmm, 1] @-}
isEven, isOdd  :: Int -> Bool

isEven 0 = True
isEven n = isOdd  $ n - 1

isOdd  k = not $ isEven k



