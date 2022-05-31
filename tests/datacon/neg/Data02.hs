module Data02 where

import Data02Lib

{-@ test4 :: Nat -> Pair @-}
test4 x = P x (x - 1)
