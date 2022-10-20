{-@ LIQUID "--expect-any-error" @-}
module SubRel where

foo :: Int -> Int
foo x = x

{-@ relational foo ~ foo :: Int -> Int ~ Int -> Int | false => false @-}

bar :: Int -> Int
bar x = foo x

{-@ relational bar ~ bar :: Int -> Int ~ Int -> Int | true => false @-}