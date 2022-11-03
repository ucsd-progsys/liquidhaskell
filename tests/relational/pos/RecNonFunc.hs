{-@ LIQUID "--no-termination" @-}

module Fixme where

{-@ r :: Nat @-}
r :: Int
r = 1 + r

{-@ relational r ~ r :: { _ ~ _ 
                     | r1 == r2 } @-}