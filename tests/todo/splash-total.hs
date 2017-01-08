module SplashTotal where

import Prelude hiding (foldr1, head)

head       :: [a] -> a
incr       :: Int -> Int
average    :: [Int] -> Int
group      :: (Eq a) => [a] -> [[a]]
foldr1     :: (a -> a -> a) -> [a] -> a
impossible :: String -> a
merge      :: Ord a => [a] -> [a] ->  [a]
fib        :: Int -> Int
ups        :: [Int]
insertSort :: (Ord a) => [a] -> [a]
insert     :: (Ord a) => a -> [a] -> [a]

-- REPLACE `-` with `+`

{-@ incr :: Nat -> Nat @-}
incr x = x - 1

{-@ impossible :: {v: String | False} -> a @-}
impossible = error

--------------------------------------------------------------------------------

-- TOTALITY A 1
{-@ type NonEmpty a = {v:[a] | len v > 0} @-}

-- replace input with NonEmpty a

{-@ head :: [a] -> a @-}
head (x:_) = x
head []    = impossible "head on empty list"

-- TOTALITY A 2

unstutter :: String -> String
unstutter = map head . group

-- replace output with NonEmpty a

{-@ group :: (Eq a) => [a] -> [[a]] @-}
group []      = []
group (x:xs)  = (x:ys) : group zs
  where
    (ys, zs)  = span (x ==) xs

--------------------------------------------------------------------------------
-- TOTALITY B 1
-- replace input with NonEmpty a
-- ADD signature: foldr1 :: (a -> a -> a) -> {v:[a] | len v > 0} -> a
foldr1 op (x:xs) = foldr op x xs
foldr1 _  _      = impossible "foldr1 on empty list"

-- TOTALITY B 2
{-@ average :: NonEmpty Int -> Int @-}
average xs = foldr1 (+) xs `div` length xs


--------------------------------------------------------------------------------

-- TERMINATION
-- ADD / [len xs + len ys]

{-@ fib :: Nat -> Nat @-}
fib 0 = 1
-- fib 1 = 1
fib n = fib (n-1) + fib (n-2)

{-@ merge :: Ord a => xs:[a] -> ys:[a] -> [a] @-}
merge xs []         = xs
merge [] ys         = ys
merge (x:xs) (y:ys)
  | x <= y          = x : merge xs (y:ys)
  | otherwise       = y : merge (x:xs) ys

--------------------------------------------------------------------------------

-- USER DEFINED INVARIANTS

{-@ type OrdList a = [a]<{\x v -> x <= v}> @-}

{-@ ups :: OrdList Int @-}
ups = [1, 2, 3, 40, 5]

{-@ insertSort :: (Ord a) => [a] -> OrdList a @-}
insertSort = foldr insert []

-- FLIP COMPARISON
{-@ insert :: (Ord a) => a -> OrdList a -> OrdList a @-}
insert x []     = [x]
insert x (y:ys)
  | x >= y      = x : y : ys
  | otherwise   = y : insert x ys

--------------------------------------------------------------------------------











--------------------------------------------------------------------------------
