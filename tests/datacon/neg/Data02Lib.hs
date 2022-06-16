{-@ LIQUID "--expect-any-error" @-}
module Data02Lib where

{-@ data Pair = P { pX :: Nat, pY :: {v:Nat | pX < v} } @-}
data Pair = P { pX :: Int, pY :: Int }

{-@ test1 :: Pair -> TT @-}
test1 (P a b) =  a < a 

