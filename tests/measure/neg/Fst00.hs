{-@ LIQUID "--expect-any-error" @-}
-- TAG: measure 
-- test if the "builtin" fst and snd measures work.

module Fst00 where

{-@ splitter :: x:Int -> {v:(Int, Int) | myFst v + mySnd v = x + 1 } @-}
splitter :: Int -> (Int, Int)
splitter x = (0, x)

joiner :: Int -> Int 
{-@ joiner :: y:Int -> {v:Int | v = y} @-}
joiner y = a + b 
  where 
    (a, b) = splitter y

{-@ measure myFst @-}
myFst (x, _) = x 

{-@ measure mySnd @-}
mySnd (_, x) = x 


