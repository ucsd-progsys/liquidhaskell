-- | This file tests that LH correctly localizes the elaboration error
--   to the '10 / x' term (where we get a sort-error as the 'Ratio Int'
--   is compared against '0' which appears in the refinement for '/'.)
--   You can fix this by `embed Ratio * as Int`

{-@ LIQUID "--expect-error-containing=ElabLocation.hs:15:14" @-}

module ElabLocation where

import Data.Ratio

foo :: Ratio Int -> Bool
foo x = y == y
  where
    y = 10 / x
