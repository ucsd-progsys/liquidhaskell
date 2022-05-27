module Alias05 where

{-@ data Zoo = Z { zA :: Int, zB :: {v:Int | less zA v} } @-} 

{-@ inline less @-}
less :: Int -> Int -> Bool
less x y = x < y

data Zoo = Z { zA :: Int, zB :: Int }

test :: Int -> Zoo 
test x = Z x (x + 1)

