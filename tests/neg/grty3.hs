module Foo () where


{-@ choo :: [a] -> {v: Int | v > 0 } @-}
choo = poo


poo :: [a] -> Int 
poo (x:xs) = poo xs
poo []     = 0
