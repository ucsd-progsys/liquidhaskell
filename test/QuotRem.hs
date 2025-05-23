-- |

module QuotRem (prop_quotRem, prop_quotRemDivision) where
import Test.QuickCheck

prop_quotRem :: Integral a => a -> a -> Property
prop_quotRem x y = y /= 0 ==> quotRem' x y == quotRem x y

{-@quotRem':: x:a -> {y:a | y /= 0} -> {z:(a,a) | fst z = quot x y && snd z = rem x y }@-}
-- | This is a definition of `quotRem` in terms of `div` and `mod`
-- used at @liquidhaskell/src/GHC/Real_LHAssumptions.hs@
-- to implement both 'quot' and 'rem' in the refinement logic.
quotRem' :: Integral a => a -> a -> (a,a)
quotRem' x y | signum x == signum y || abs x == abs y = (div x y, mod x y)
             | abs x > abs y = (- (div x y), x + y * div x y)
             | otherwise = (0, x)

prop_quotRemDivision :: Integral a => a -> a -> Property
prop_quotRemDivision x y = y/= 0 ==> x == q * y + r
  where (q,r) = quotRem' x y
