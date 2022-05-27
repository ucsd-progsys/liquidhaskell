module Alias04 where

{-@ predicate Less X Y = X < Y @-} 

{-@  data Zoo = Z { zA :: Int, zB :: {v:Int | Less zA v} } @-} 

data Zoo = Z { zA :: Int, zB :: Int }

test :: Int -> Zoo 
test x = Z x (x + 1)

