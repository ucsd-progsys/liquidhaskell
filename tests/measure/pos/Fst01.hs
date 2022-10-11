-- TAG: measure 
-- test if the "builtin" fst and snd measures work.

module Fst01 where

{-@ splitter :: x:Int -> {v:(Int, Int) | fst v + snd v = x } @-}
splitter :: Int -> (Int, Int)
splitter x = (0, x)

joiner :: Int -> Int 
{-@ joiner :: y:Int -> {v:Int | v = y} @-}
joiner y = a + b 
  where 
    (a, b) = splitter y
