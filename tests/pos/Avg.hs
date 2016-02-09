module Avg where

{-@ measure sumD :: [Double] -> Double
    sumD([]) = 0.0
    sumD(x:xs) = x + (sumD xs)
  @-}

{-@ measure lenD :: [Double] -> Double
    lenD([]) = 0.0
    lenD(x:xs) = (1.0) + (lenD xs)
  @-}

{-@ expression Avg Xs = ((sumD Xs) / (lenD Xs))  @-}

{-@ meansD :: xs:{v:[Double] | ((lenD v) > 0.0)} 
           -> {v:Double | v = Avg xs} @-}
meansD :: [Double] -> Double
meansD xs = sumD xs / lenD xs

{-@ lenD :: xs:[Double] -> {v:Double | v = (lenD xs)} @-}
lenD :: [Double] -> Double
lenD [] = 0.0
lenD (x:xs) = 1.0 + lenD xs

{-@ sumD :: xs:[Double] -> {v:Double | v = (sumD xs)} @-}
sumD :: [Double] -> Double
sumD [] = 0.0
sumD (x:xs) = x + sumD xs
