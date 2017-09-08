{-@ LIQUID "--prune-unsorted" @-}

module Avg where

{-@ measure sumF :: [Double] -> Double
    sumF([]) = 0.0
    sumF(x:xs) = x + (sumF xs)
  @-}

{-@ measure lenF :: [Double] -> Double
    lenF([])   = 0.0
    lenF(x:xs) = (1.0) + (lenF xs)
  @-}

{-@ expression Avg Xs = ((sumF Xs) / (lenF Xs))  @-}

{-@ meansD :: xs:{v:[Double] | 0.0 < lenF v } -> {v:Double | v = Avg xs} @-}
meansD :: [Double] -> Double
meansD xs = sumD xs / lenD xs

{-@ lenD :: xs:[Double] -> {v:Double | v = lenF xs } @-}
lenD :: [Double] -> Double
lenD [] = 0.0
lenD (x:xs) = 1.0 + lenD xs

{-@ sumD :: xs:[Double] -> {v:Double | v = sumF xs } @-}
sumD :: [Double] -> Double
sumD [] = 0.0
sumD (x:xs) = x + sumD xs
