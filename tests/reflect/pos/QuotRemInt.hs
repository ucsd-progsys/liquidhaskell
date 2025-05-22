-- | Reflection of a function using `quot` and `rem` was not working,
-- because they were not defined in the refinement logic until
-- https://github.com/ucsd-progsys/liquidhaskell/pull/2540
-- to fix
-- https://github.com/ucsd-progsys/liquidhaskell/issues/1447

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

{-@ sumId :: x : Int -> y : Int -> {z : Int | z = x + y}@-}
sumId' :: Int -> Int -> Int
sumId' x y =  intId' x + intId' y
