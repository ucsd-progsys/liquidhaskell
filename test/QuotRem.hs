-- |

module QuotRem (prop_quotRemAltEuclideanDomain, prop_quotRemAlt) where
import Test.QuickCheck ( (==>), Property )

prop_quotRemAltEuclideanDomain :: Integer -> Integer -> Property
prop_quotRemAltEuclideanDomain x y = y/= 0 ==> x == q * y + r && (0 == r || abs r < abs y)
  where (q,r) = quotRem'' x y

prop_quotRemAlt :: Integer -> Integer -> Property
prop_quotRemAlt x y = y /= 0 ==> quotRem'' x y == quotRem x y

{-@quotRem':: x:a -> {y:a | y /= 0} -> {z:(a,a) | fst z = quot x y && snd z = rem x y }@-}
-- | An implementation of 'quotRem', which is a primitive in the standard library.
quotRem' :: (Integral a) => a -> a -> (a, a)
quotRem' x y = case (signum x, signum y) of
  (-1, -1) -> second negate $ quotRemIter (-x) (-y) 0
  (1, -1) -> first negate $ quotRemIter x (-y) 0
  (-1, 1) -> both negate $ quotRemIter (-x) y 0
  (1, 1) -> quotRemIter x y 0
  (_, 0) -> error "quotRem': divide by zero"
  (0, _) -> (0, 0)

{-@quotRem'':: x:a -> {y:a | y /= 0} -> {z:(a,a) | fst z = quot x y && snd z = rem x y }@-}
-- | A variant of 'quotRem' implemented in terms of 'divMod' to check that the
-- equivalent definitions of `quot` and `rem` for the refinement logic
-- found at @liquidhaskell/src/GHC/Real_LHAssumptions.hs@ are correct.
-- This assumes that the functions @/@ and @mod@ from liquid-fixpoint
-- behave as Haskell's 'div' and 'mod' respectively.
quotRem'' :: (Integral a) => a -> a -> (a, a)
quotRem'' x y = case (signum x, signum y) of
  (1, -1) -> first negate $ divMod x (-y)
  (-1, 1) -> both negate $ divMod (-x) y
  (_,_) -> divMod x y


first :: (a -> a') -> (a,b) -> (a',b)
first f (x, y) = (f x, y)

second :: (b -> b') -> (a,b) -> (a,b')
second f (x, y) = (x, f y)

both :: (a -> b) -> (a,a) -> (b,b)
both f (x, y) = (f x, f y)

{-@ quotRemIter :: (Integral a) => {x:a | x >= 0}
                                -> {y:a | y > 0}
                                -> {q:a | q >= 0}
                                -> {z:(a,a) | fst z = x / y && snd = x mod y} @-}
-- | A non-total and straight-forward implementation of the division algorithm on
-- positive values. This function behaves as 'divMod' and 'quotRem' if the first
-- and third arguments are natural and the second positive.
quotRemIter :: Integral a => a -> a -> a -> (a,a)
quotRemIter a b q =
  if a - b * q < b
    then (q, a - b * q)
    else quotRemIter a b (q + 1)


