module Fixme where

foo :: Int -> Int
foo = succ

{-@ relational foo ~ foo :: {v:(x1:Int -> Int) | 0 /= 0} ~ x2:Int -> Int ~~ x1 == x1 @-}
