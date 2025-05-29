{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-- | Properties for testing the definitions of @quot@ and @rem@ found at
-- @liquidhaskell/src/GHC/Real_LHAssumptions.hs@.
module QuotRem (tests) where

import Test.QuickCheck ( (==>), Property )
import Test.Tasty (testGroup, TestTree)
import Test.Tasty.QuickCheck (testProperty)

tests :: TestTree
tests = testGroup "QuotRem"
    [ testProperty "divSMT and modSMT are consistent" prop_divModSMTEuclideanDivision
    , testProperty "quotSMT and remSMT are consistent" prop_quotRemAltEuclideanDivision
    , testProperty "quotRem behaves as quotSMT and remSMT" prop_quotRemAlt
    ]

{-@ ignore prop_divModSMTEuclideanDivision @-}
prop_divModSMTEuclideanDivision :: Int -> Int -> Property
prop_divModSMTEuclideanDivision a b = b/= 0 ==> a == d * b + m && abs m < abs b
  where (d,m) = (divSMT a b, modSMT a b)

{-@ ignore prop_quotRemAltEuclideanDivision @-}
prop_quotRemAltEuclideanDivision :: Int -> Int -> Property
prop_quotRemAltEuclideanDivision a b = b/= 0 ==> a == q * b + r && abs r < abs b
  where (q,r) = (quotSMT a b, remSMT a b)

{-@ ignore prop_quotRemAlt @-}
prop_quotRemAlt :: Int -> Int -> Property
prop_quotRemAlt a b = b /= 0 ==> (quotSMT a b, remSMT a b) == quotRem a b

{-@
quotSMT :: a:Int
      -> {b:Int | b != 0}
      -> {v:Int | v = quot a b} @-}
-- | A variant of 'quot' implemented in terms of 'divSMT'.
quotSMT :: Int -> Int -> Int
quotSMT a b
  | a >= 0 = if b >= 0 then divSMT a b else - divSMT a (- b)
  | otherwise = - divSMT (- a) b

{-@
remSMT :: a:Int
     -> {b:Int | b != 0}
     -> {v:Int | v = rem a b}
@-}
-- | A variant of 'rem' implemented in terms 'modSMT'.
remSMT :: Int -> Int -> Int
remSMT a b
  | a >= 0 = if b >= 0 then modSMT a b else  modSMT a (- b)
  | otherwise = - modSMT (- a) b

{-@
modSMT
  :: a:Int
  -> {b:Int | b != 0}
  -> {v:Int | v = a mod b}
@-}
-- | Refinement logic @mod@.
modSMT :: Int -> Int -> Int
modSMT a b = a - b * divSMT a b

{-@
divSMT
  :: a:Int
  -> {b:Int| b != 0}
  -> {v:Int | v = a / b} / [ divSMTTermination a b ]
@-}
-- | The defining property of divSMT is
--
-- > 0 <= a - divSMT a b * b && a - divSMT a b * b < abs b
--
-- or in terms of mod
--
-- > 0 <= modSMT a b && modSMT a b < abs b
--
divSMT :: Int -> Int -> Int
divSMT a 0 = error "divide by zero"
divSMT a b
      -- a satisfies the defining property
    | a < abs b && 0 <= a = 0
      -- equal signs
    | a > 0 && b > 0 || a < 0 && b < 0 =
        1 + divSMT (a - b) b
      -- distinct signs
    | otherwise =
        divSMT (a + b) b - 1

{-@ inline divSMTTermination @-}
divSMTTermination :: Int -> Int -> Int
divSMTTermination a b
  | a >= 0    = a
  | otherwise = abs b - a
