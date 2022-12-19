module Fixme where

f :: Int -> Int
f x = if x <= 0 then 0 else 1 + f (x - 1)

f' :: Int -> Int
f' x = if x <= 0 then 0 else 1 + f' (x - 1)

{-@ relational f ~ f' :: {x1:_ -> _ ~ x2:_ -> _
                     | x1 == x2 :=> r1 x1 >= 0 && r2 x2 >= 0} @-}
