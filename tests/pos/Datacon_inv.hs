module Datacon_inv where

data T =  A | B

{-@ invariant {v:T | (v = A || v = B)} @-}

thisIsA = A
thisIsB = B
