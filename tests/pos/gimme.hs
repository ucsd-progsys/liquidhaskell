module Blank () where

import Language.Haskell.Liquid.Prelude

{- qualif Gimme(v:[a], n:int, acc:[a]): (len v == n + 1 + len acc) -}

{-@ gimme :: xs:[a] -> n:Int -> acc:[a] -> {v:[a] | len v = n + 1 + len acc} @-}
gimme :: [a] -> Int -> [a] -> [a]
gimme xs (-1) acc  = acc
gimme (x:xs) n acc = gimme xs (n-1) (x : acc)
gimme _ _ _        = unsafeError "gimme"

{-@ boober :: n:Int -> Int -> {v:[Int] | (len v) = n} @-}
boober :: Int -> Int -> [Int]
boober n y = gimme [y..] (n-1) []
