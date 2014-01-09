{--! run liquid with no-termination -}
module Blank () where

-- This is a blank file.

{- foo :: xs:[Int] -> {v:[Int] | (len v) = (len xs)} @-}
foo :: [Int] -> [Int]
foo []     = []
foo (x:xs) = (x+1) : foo [y | y <- xs] 

{- qsort :: (Ord a) => xs:[a] -> {v:[a] | (len v) <= (len xs)} @-}
qsort []     = []
qsort (x:xs) = x : qsort [y | y <- xs, y < x]

{-@ quickSort    :: (Ord a) => [a] -> SList a @-}
quickSort []       = []
quickSort xs@(x:_) = append x lts gts 
  where 
    lts          = quickSort [y | y <- xs, y < x]
    gts          = quickSort [z | z <- xs, z >= x]

{- append :: k:a -> SList {v:a | v<k} -> SList {v:a | v >= k} -> SList a @-}
append k []     ys  = k : ys
append k (x:xs) ys  = x : append k xs ys

{-@ type SList a = [a]<{\x v -> (v >= x)}> @-}

