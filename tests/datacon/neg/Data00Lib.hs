{-@ LIQUID "--expect-any-error" @-}
module Data00Lib where

{-@ data Thing = Thing { fldThing :: {v:Int | 0 <= v} } @-}
data Thing = Thing { fldThing :: Int }

test2 :: Int -> Thing 
test2 = Thing 


