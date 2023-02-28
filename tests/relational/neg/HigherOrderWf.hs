{-@ LIQUID "--expect-any-error" @-}
module HigherOrderWf where

foo :: Int -> (Int -> Int) -> Int
foo x _ = x

bar :: Int -> (Int -> Int -> Int) -> Int
bar x _ = x

{-@ relational foo ~ bar :: { Int -> (Int -> Int) -> Int
                            ~ Int -> (Int -> Int -> Int) -> Int
                            | (true) :=> true } @-}
