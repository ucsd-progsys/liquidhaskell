module MutRec () where

{-@ isEven :: Nat -> {v:Int | v = 0} -> Bool @-}
{-@ Decrease isEven 1 2 @-}
isEven :: Int -> Int -> Bool
isEven 0 _ = True
isEven n _ = isOdd (n-1) 1

{-@ isOdd :: Nat -> {v:Int | v = 1} -> Bool @-}
{-@ Decrease isOdd 1 2 @-}
isOdd :: Int -> Int -> Bool
isOdd  n _ = not $ isEven n 0
