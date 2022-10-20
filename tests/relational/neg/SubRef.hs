{-@ LIQUID "--expect-any-error" @-}
module SubRef where

foo :: Int -> Int
foo x = x

{-@ relational foo ~ foo :: {x:Int|false} -> Int ~ Int -> Int | true => false @-}

bar :: Int -> Int
bar x = foo x

{-@ relational bar ~ bar :: Int -> Int ~ Int -> Int | true => false @-}