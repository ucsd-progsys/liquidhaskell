-- This test checks whether "invariants" are working.

module List02Lib where

data List yy
  = Emp 
  | Cons yy (List yy)

{-@ type NN = {v:Int | 0 <= v} @-}

{-@ measure size @-}
{-@ size :: List zoob -> NN @-}
size :: List zoob -> Int 
size Emp         = 0 
size (Cons _ xs) = 1 + size xs 

{-@ test :: xs:List a -> {v:Int | v = size xs} -> NN @-}
test :: List a -> Int -> Int 
test xs n = n 
