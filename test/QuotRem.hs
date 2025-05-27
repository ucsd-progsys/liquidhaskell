{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
-- |

module QuotRem (prop_quotRemAltEuclideanDomain, prop_quotRemAlt) where
import Test.QuickCheck ( (==>), Property )

{-@ prop_quotRemAltEuclideanDomain :: x:Int -> {y:Int | y /= 0} -> Property @-}
prop_quotRemAltEuclideanDomain :: Int -> Int -> Property
prop_quotRemAltEuclideanDomain x y = y/= 0 ==> x == q * y + r && (0 == r || abs r < abs y)
  where (q,r) = quotRem' x y

{-@ prop_quotRemAlt :: x:Int -> {y:Int | y /= 0} -> Property @-}
prop_quotRemAlt :: Int -> Int -> Property
prop_quotRemAlt x y = y /= 0 ==> quotRem' x y == quotRem x y

{-@ quotRem' :: x:Int -> {y:Int | y /= 0}
                      -> {z:(Int,Int) | fst z = quot x y && snd z = rem x y} @-}
-- | A variant of 'quotRem' implemented in terms of functions equivalent
-- to @/@ and @mod@ of the refinement logic.
-- This is an /inverse reflection/ test to show the definitions of logic `quot` and `rem`
-- found at @liquidhaskell/src/GHC/Real_LHAssumptions.hs@ are correct.
quotRem' ::  Int -> Int -> (Int, Int)
quotRem' x y = (quot' x y, rem' x y)

{-@ quot' :: x:Int -> {y:Int | y /= 0} -> {z:Int | z = quot x y} @-}
quot' :: Int -> Int -> Int
quot' x y
  | x >= 0 = if y >= 0 then div' x y else - div' x (abs y)
  | otherwise = - div' (abs x) y
  where div' x y = fst $ divModSMT x y

{-@ rem' :: x:Int -> {y:Int | y /= 0} -> {z:Int | z = rem x y} @-}
rem' :: Int -> Int -> Int
rem' x y
  | x >= 0 = if y >= 0 then mod' x y else  mod' x (abs y)
  | otherwise = - mod' (abs x) y
  where mod' x y = snd $ divModSMT x y

{-@ define signum x = if x>0 then 1 else (if x<0 then -1 else 0) @-}

{-@ divModSMT :: x:Int -> {y:Int | y /= 0}
                       -> {z:(Int,Int) | fst z = x / y && snd z = x mod y} @-}
-- | A Haskell implementation of logic @/@ and @mod@.
-- Most notably, `mod` is always positive.
divModSMT :: Int -> Int -> (Int, Int)
divModSMT = divModIter 0

{-@ divModIter :: Int -> x:Int -> {y:Int | y /= 0}
                      -> {z:(Int,Int) | fst z = x / y && snd z = x mod y} @-}
divModIter :: Int -> Int -> Int -> (Int,Int)
divModIter q a 0 = error "divide by zero"
divModIter q 0 b = (0, 0)
divModIter q a b =
  if abs (a - b * q) < abs b && (b * q <= a)
    then (q, a - b * q)
    else divModIter (q + signum (a * b)) a b
