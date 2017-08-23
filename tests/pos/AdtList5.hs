-- | The current code for lifting ADTs cannot deal with the case when there
--   are "holes" in the data-decl specification, presumably because the lifting
--   happens BEFORE the holes are resolved.

{-@ LIQUID "--exact-data-cons" @-}

module AdtList where

data Zing = ZZ (Int -> ())

{-@ data Zing = ZZ { unZZ :: Int -> { 5 < 10 } } @-}

{-@ bob :: Nat @-}
bob :: Int
bob = 12
