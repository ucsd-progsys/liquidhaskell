module ReflectClient0 where

import ReflectLib0


-- the below works with GreaterThanA instead of GreaterThan,
-- as the former is defined as a "predicate" alias.

{-@ incr :: x:Nat -> {v:Nat | gtThan v x} @-}
incr :: Int -> Int
incr x = x + 1


-- {-@ reflect floog @-}
-- floog :: Int -> Int -> Bool
-- floog x y = gtThan x y
