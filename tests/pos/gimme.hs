module Blank () where

{-@ qualif Gimme(v:a, n:b, acc:a): len v = n + 1 + len acc @-}

gimme :: [a] -> Int -> [a] -> [a]
gimme xs (-1) acc  = acc
gimme (x:xs) n acc = gimme xs (n-1) (x : acc)
gimme _ _ _        = error "gimme"

{-@ boober :: n:Int -> Int -> {v:[Int] | (len v) = n} @-}
boober :: Int -> Int -> [Int]
boober n y = gimme [y..] (n-1) []
