module Data00 where

import Data00Lib 

{-@ test3 :: Thing -> Nat @-}
test3 :: Thing -> Int
test3 (Thing x) = x 

{-@ test4 :: Nat -> Thing @-}
test4 :: Int -> Thing 
test4 = Thing 


