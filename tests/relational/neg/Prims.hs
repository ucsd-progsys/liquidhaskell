{-@ LIQUID "--expect-any-error" @-}
module Fixme where

i :: Int
i = 0

b :: Bool
b = True

{-@ relational i ~ b :: Int ~ Bool
                     | r2 <=> r1 /= 0 @-}