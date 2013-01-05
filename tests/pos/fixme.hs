module Fixme where

{-@ type IntLess i = {v:Int | (i < v)} @-}

-- this is safe
{-@ foo :: i:Int  -> (IntLess i) @-}
foo     :: Int -> Int
foo n   = n + 1

{-@ bar :: n:Int  -> (IntLess n) @-}
bar     :: Int -> Int
bar n   = n + 1
