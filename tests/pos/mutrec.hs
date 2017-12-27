module MutRec () where

{-@ isEven :: n:Nat -> z:{v:Int | v = 0} -> Bool / [n, z] @-}
isEven :: Int -> Int -> Bool
isEven 0 _ = True
isEven n _ = isOdd (n-1) 1

{-@ isOdd :: n:Nat -> z:{v:Int | v = 1} -> Bool / [n, z] @-}
isOdd :: Int -> Int -> Bool
isOdd  n _ = not $ isEven n 0


{- decrease isEven 1 2 -}
{- decrease isOdd 1 2  -}
