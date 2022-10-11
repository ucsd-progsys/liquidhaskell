module Data02Lib where

{-@ data Pair = P { pX :: Nat, pY :: {v:Nat | pX < v} } @-}
data Pair = P { pX :: Int, pY :: Int }

{-@ test1 :: Pair -> TT @-}
test1 (P a b) =  a < b 

{-@ test2 :: Nat -> Pair @-}
test2 x = P x (x + 1)


