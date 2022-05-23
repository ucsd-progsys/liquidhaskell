module Alias03 where

{-@ type Less X = {v:Int | X < v}  @-} 
{-@ data Zoo = Z { zA :: Int, zB :: Less zA } @-} 

data Zoo = Z { zA :: Int, zB :: Int }

test :: Int -> Zoo 
test x = Z x (x + 1)

