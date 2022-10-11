{-@ LIQUID "--reflection" @-}
module T1543 where

foo :: (Int -> Int) ->  (Int -> Int, ())
{-@ foo :: f:(Int -> Int) ->  (g::(Int -> Int),{v:() | f == g}) @-}
foo f = (f,()) 
