module Data.KMeans where

dist ::  [Double] -> [Double] -> [Double]
dist a b = zipWith (\ x y -> x + y) a b 
