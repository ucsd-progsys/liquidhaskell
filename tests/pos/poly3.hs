module Meas () where

expand          :: (a -> [b]) -> [a] -> [b]
expand f []     = []
expand f (x:xs) = (f x) ++ (expand f xs)

baz :: a -> [Int]
baz _ = [0]

goo = expand baz

