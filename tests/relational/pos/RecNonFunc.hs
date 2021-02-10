{-@ LIQUID "--no-termination" @-}

module Fixme where

r :: Int
r = 1 + r

{-@ relational r ~ r :: Nat ~ Nat 
                     ~~ r1 > 0 && r2 > 0 @-}