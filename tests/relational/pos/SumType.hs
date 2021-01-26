module Fixme where

data D = A | B | C

foo :: D -> Int
foo A = 0
foo _ = 2

bar :: D -> Int
bar A = 1
bar _ = 3

{-@ relational foo ~ bar :: x1:D -> Int ~ x2:D -> Int
                         ~~ x1 == x2 => r1 x1 < r2 x2 @-}