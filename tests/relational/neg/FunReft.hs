{-@ LIQUID "--expect-any-error" @-}
module Fixme where

{-@ foo :: { v:(x1:Int -> Int) | x1 /= x1 } @-}
foo :: Int -> Int
foo = succ

{-@ relational foo ~ foo :: {x1:Int -> Int ~ x2:Int -> Int 
                         | x1 == x2 :=> r1 x1 == r2 x2 || r1 x1 /= r2 x2  } @-}
