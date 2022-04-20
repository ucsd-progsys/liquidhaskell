module Data00Lib where

{-@ data Thing = Thing { fldThing :: {v:Int | 0 <= v} } @-}
data Thing = Thing { fldThing :: Int }


{-@ test1 :: Thing -> Nat @-}
test1 :: Thing -> Int
test1 (Thing x) = x 

{-@ test2 :: Nat -> Thing @-}
test2 :: Int -> Thing 
test2 = Thing 


