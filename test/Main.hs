-- |

module Main where

import Control.Monad (unless)
import QuotRem (prop_quotRemAltEuclideanDomain, prop_quotRemAlt)
import System.Exit (exitFailure)
import Test.QuickCheck (quickCheck, verboseCheck, quickCheckResult, isSuccess)

main :: IO ()
main = do
        quickCheck prop_quotRemAltEuclideanDomain
        quickCheck prop_quotRemAlt

-- | Throws error if a test fails. Use this alternative to abort build
-- in case of failure when test condition is enabled.
main' :: IO ()
main' = do
  let tests =
        [ quickCheckResult prop_quotRemAltEuclideanDomain
        , quickCheckResult prop_quotRemAlt
        ]
  success <- fmap (all isSuccess) . sequence $ tests
  unless success exitFailure
