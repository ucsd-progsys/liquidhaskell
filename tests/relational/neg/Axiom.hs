{-@ LIQUID "--expect-any-error" @-}
module Axiom where

foo :: Int -> Int
foo x = x

bar :: Int -> Int
bar x = x

{-@ relational foo ~ bar :: {x1:Int -> Int ~ x2:Int -> Int 
                         | x1 /= x2 |- true :=> r1 x1 = r2 x2} @-}