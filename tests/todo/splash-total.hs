module SplashTotal where

import Prelude hiding (foldr1, group, head)

incr :: Int -> Int
average :: [Int] -> Int

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
