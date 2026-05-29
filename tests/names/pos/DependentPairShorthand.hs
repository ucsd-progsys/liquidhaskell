-- | Regression test for https://github.com/ucsd-progsys/liquidhaskell/issues/2590
-- Shorthand refinement syntax in function types inside dependent pair
-- components should not crash.
module DependentPairShorthand where

{-@ bar :: (n::Nat, Int -> { n >= 0 }) @-}
bar :: (Int, Int -> ())
bar = (0, \_ -> ())
