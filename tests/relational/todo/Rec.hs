module Fixme where

f = f
g = g

{-@ relational f ~ g :: x1:a ~ x2:a
                     ~~ true => r1 x1 == r2 x2 @-}
