-- | Regression test for https://github.com/ucsd-progsys/liquidhaskell/issues/2590
-- Shorthand refinement syntax in function types inside dependent pair
-- components should not crash.
module DependentPairShorthand where

import Language.Haskell.Liquid.ProofCombinators

{-@ bar :: (n::Nat, Int -> { n >= 0 }) @-}
bar :: (Int, Int -> Proof)
bar = (0, \_ -> trivial)
