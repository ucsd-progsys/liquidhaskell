-- |

module Main where

import Control.Monad (unless)
import QuotRem (prop_quotRem, prop_quotRemDivision)
import System.Exit (exitFailure)
import Test.QuickCheck (quickCheck, verboseCheck, quickCheckResult, isSuccess)

main :: IO ()
main = do
        verboseCheck prop_quotRemDivision
        verboseCheck prop_quotRem

-- | Throws error if a test fails.
main' :: IO ()
main' = do
  let tests =
        [ quickCheckResult prop_quotRemDivision
        , quickCheckResult prop_quotRem
        ]
  success <- fmap (all isSuccess) . sequence $ tests
  unless success exitFailure
