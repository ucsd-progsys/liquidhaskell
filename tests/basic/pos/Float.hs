module Foo where


{-@ r :: {v:Float | v > 0} @-}
r :: Float
r = 0.014 

cmp :: Bool 
cmp = r > 0 