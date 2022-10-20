module Fixme where

s :: Int 
s = 0

b :: Bool
b = True

{-@ relational s ~ b :: Int ~ Bool
                     | r2 <=> (r1 == 0) @-}