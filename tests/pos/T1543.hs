{-@ LIQUID "--reflection" @-}
module Fixme where

foo :: (Int -> Int) ->  (Int -> Int, ())
{-@ foo :: f:(Int -> Int) ->  (g::(Int -> Int),{v:() | f == g}) @-}
foo f = (f,()) 
