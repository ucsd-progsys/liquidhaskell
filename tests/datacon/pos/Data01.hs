module Data01 where

{-@ data Thing = Thing { fldThing :: Nat } @-}
data Thing = Thing { fldThing :: Int }


{-@ test1 :: Thing -> Nat @-}
test1 :: Thing -> Int
test1 (Thing x) = x 

{-@ test2 :: Nat -> Thing @-}
test2 :: Int -> Thing 
test2 = Thing 


