{-@ LIQUID "--expect-any-error" @-}
module FunBaseWf where

foo :: Int -> Int
foo x = x

x :: Int
x = 0

{-@ relational foo ~ x :: { x1:Int -> Int 
                          ~ Int
                          | true } @-}
