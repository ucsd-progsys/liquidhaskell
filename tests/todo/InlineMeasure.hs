{-@ LIQUID "--short-names"    @-}

module InlineMeasures where

mmax       :: Int -> Int -> Int
mmax x y   = if x > y then x else y

{-@ measure foo @-}
foo :: [Int] -> Int
foo []     = 0
foo (x:xs) = if (x > 0) then x else 0 

{-@ measure bar @-}
bar :: [Int] -> Int
bar [] = 0
bar (x:xs) = mmax x 0
