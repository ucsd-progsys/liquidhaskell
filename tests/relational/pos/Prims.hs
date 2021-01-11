module Fixme where

s :: Int 
s = 0

b :: Bool
b = True

{-@ relational s ~ b :: {v:Int|v == 0} ~ Bool
                     ~~ r2 <=> (r1 == 0) @-}