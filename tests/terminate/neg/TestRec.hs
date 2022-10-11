{-@ LIQUID "--expect-any-error" @-}
module TestRec where

import Prelude hiding (map, foldl)

{-@ map :: (a -> b) -> [a] -> [b] @-}
map :: (a -> b) -> [a] -> [b] 
map f []     = []
map f (x:xs) = f x : map f (x:xs)
