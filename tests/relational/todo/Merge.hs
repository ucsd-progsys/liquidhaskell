module Fixme where

{-@ merge :: xs:[Int] -> ys:[Int] -> {v:[Int]|len v == len xs + len ys} @-}
merge :: [Int] -> [Int] -> [Int]
merge [] ys                        = ys
merge xs []                        = xs
merge (x : xs) ys@(y : _) | x <= y = x : merge xs ys
merge xs (y : ys)                  = y : merge xs ys

