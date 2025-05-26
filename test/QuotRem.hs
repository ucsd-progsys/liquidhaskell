{-@ LIQUID "--reflection" @-}
-- |

module QuotRem (prop_quotRemAltEuclideanDomain, prop_quotRemAlt) where
import Test.QuickCheck ( (==>), Property )

prop_quotRemAltEuclideanDomain :: Integer -> Integer -> Property
prop_quotRemAltEuclideanDomain x y = y/= 0 ==> x == q * y + r && (0 == r || abs r < abs y)
  where (q,r) = quotRem' x y

prop_quotRemAlt :: Integer -> Integer -> Property
prop_quotRemAlt x y = y /= 0 ==> quotRem' x y == quotRem x y

{-@quotRem':: x:a -> {y:a | y /= 0} -> {z:(a,a) | fst z = quot x y && snd z = rem x y }@-}
-- | A variant of 'quotRem' implemented in terms of 'divMod' to check that the
-- equivalent definitions of `quot` and `rem` for the refinement logic
-- found at @liquidhaskell/src/GHC/Real_LHAssumptions.hs@ are correct.
-- This assumes that the functions @/@ and @mod@ from liquid-fixpoint
-- behave as Haskell's 'div' and 'mod' respectively.
quotRem' :: (Integral a) => a -> a -> (a, a)
quotRem' x y = case (signum x, signum y) of
  (1, -1) -> first negate $ divMod x (-y)
  (-1, 1) -> both negate $ divMod (-x) y
  (_,_) -> divMod x y

{-@ define signum x = if x>0 then 1 else (if x<0 then -1 else 0)@-}

{-@ inline first@-}
first :: (a -> a') -> (a,b) -> (a',b)
first f (x, y) = (f x, y)

{-
{-@ inline second@-}
second :: (b -> b') -> (a,b) -> (a,b')
second f (x, y) = (x, f y)
-}

{-@ inline both@-}
both :: (a -> b) -> (a,a) -> (b,b)
both f (x, y) = (f x, f y)
