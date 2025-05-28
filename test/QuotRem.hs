{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-- | Properties for testing the definitions of @quot@ and @rem@ found at
-- @liquidhaskell/src/GHC/Real_LHAssumptions.hs@.
module QuotRem (prop_quotRemAltEuclideanDivision, prop_quotRemAlt) where
import Test.QuickCheck ( (==>), Property )

{-@ ignore prop_quotRemAltEuclideanDivision @-}
prop_quotRemAltEuclideanDivision :: Int -> Int -> Property
prop_quotRemAltEuclideanDivision x y = y/= 0 ==> x == q * y + r && (0 == r || abs r < abs y)
  where (q,r) = quotRemSMT x y

{-@ ignore prop_quotRemAlt @-}
prop_quotRemAlt :: Int -> Int -> Property
prop_quotRemAlt x y = y /= 0 ==> quotRemSMT x y == quotRem x y

{-@ ignore quotRemSMT @-}
-- | A variant of 'quotRem' that depends on functions equivalent
-- to @/@ and @mod@ from the refinement logic.
-- Used in 'prop_quotRemAltEuclideanDivision' and 'prop_quotRemAlt'
-- to test the definitions of logic `quot` and `rem`
-- found at @liquidhaskell/src/GHC/Real_LHAssumptions.hs@.
-- This is somewhat of an /inverse reflection/ test to prove their correctness.
quotRemSMT ::  Int -> Int -> (Int, Int)
quotRemSMT a b = (quotSMT a b, remSMT a b)

{-@
quotSMT :: a:Int
      -> {b:Int | b != 0}
      -> {v:Int | v = quot a b} @-}
-- | A variant of 'quot' implemented in terms of 'divSMT'.
quotSMT :: Int -> Int -> Int
quotSMT a b
  | a >= 0 = if b >= 0 then divSMT a b else - divSMT a (abs b)
  | otherwise = - divSMT (abs a) b

{-@
remSMT :: a:Int
     -> {b:Int | b != 0}
     -> {v:Int | v = rem a b}
@-}
-- | A variant of 'rem' implemented in terms 'modSMT'.
remSMT :: Int -> Int -> Int
remSMT a b
  | a >= 0 = if b >= 0 then modSMT a b else  modSMT a (abs b)
  | otherwise = - modSMT (abs a) b

{-@
modSMT
  :: a:Int
  -> {b:Int | b != 0}
  -> {v:Int | v = a mod b}
@-}
-- | A Haskell implementation of logic @/@ and @mod@.
modSMT :: Int -> Int -> Int
modSMT x y = x - y * divSMT x y

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
