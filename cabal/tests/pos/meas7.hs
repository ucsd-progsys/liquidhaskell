module Meas where

mylen          :: [a] -> Int
mylen []       = 0
mylen (_:xs)   = 1 + mylen xs


{-@ foo :: [a] -> {v: Int | v = 0} @-}
foo :: [a] -> Int
foo zs = case zs of
           (x:xs) -> 0
           _      -> mylen zs
