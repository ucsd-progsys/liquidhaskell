{-@ LIQUID "--expect-any-error" @-}
module Data01 where

{-@ data Thing = Thing { fldThing :: Nat } @-}
data Thing = Thing { fldThing :: Int }


test2 :: Int -> Thing 
test2 = Thing 


