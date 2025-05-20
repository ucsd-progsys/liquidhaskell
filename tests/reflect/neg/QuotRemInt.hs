{-@ LIQUID "--expect-any-error" @-}
-- | Reflection of a function using `quot` and `rem` does not work,
-- while a variant using `div` and `mod` does.
-- Both 'quot' and 'rem' are opaque-reflected.
--cf. https://github.com/ucsd-progsys/liquidhaskell/issues/1447

module QuotRemInt where

{-@ reflect intId @-}
-- | This does not work
intId :: Int -> Int
intId x = (x `quot` 2) * 2 + (x `rem` 2)

{-@ reflect intId' @-}
-- | This works
intId' :: Int -> Int
intId' x = (x `div` 2) * 2 + (x `mod` 2)

{-@ sumId :: x : Int -> y : Int -> {z : Int | z = x + y}@-}
sumId :: Int -> Int -> Int
sumId x y =  intId x + intId y
