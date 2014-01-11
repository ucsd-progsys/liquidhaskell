
module Meas () where

-- some tests for the 'expandDefaultCase' trick to case-split 
-- on the "missing" constructors.


mylen          :: [a] -> Int
mylen []       = 0
mylen (_:xs)   = 1 + mylen xs


{-@ foo :: [a] -> {v: Int | v = 0} @-}
foo :: [a] -> Int
foo zs = case zs of
           (x:xs) -> 0
           _      -> mylen zs


{-@ bar :: [a] -> {v: Int | v > 0} @-}
bar :: [a] -> Int
bar zs = case zs of
           [] -> 1
           _  -> mylen zs

