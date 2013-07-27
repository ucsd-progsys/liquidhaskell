module Blank where

-- This is a blank file.

{-@ foo :: xs:[Int] -> {v:[Int] | (len v) = (len xs)} @-}
foo :: [Int] -> [Int]
foo []     = []
foo (x:xs) = (x+1) : foo [y | y <- xs] 
