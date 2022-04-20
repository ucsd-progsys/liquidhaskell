module Data02 where

import Data02Lib 

{-@ test3 :: Pair -> TT @-}
test3 (P a b) =  a < b 

{-@ test4 :: Nat -> Pair @-}
test4 x = P x (x + 1)

