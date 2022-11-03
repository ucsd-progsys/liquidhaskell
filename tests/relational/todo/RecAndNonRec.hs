module Fixme where

f :: Int -> Int
f x = if x <= 0 then 0 else 1 + f (x - 1)

g :: Int -> Int
g x = if x <= 0 then 0 else x

{-@ relational f ~ g :: {x1:_ -> _ ~ x2:_ -> { v:Int | ((x2 <= 0) <=> (v == 0))
                                                    && ((x2 > 0) <=> (v == x2)) }
                     | x1 == x2 :=> r1 x1 == r2 x2} @-}
