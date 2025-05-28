-- |

module Main where

import Control.Monad (unless)
import QuotRem (prop_divModSMTEuclideanDivision, prop_quotRemAltEuclideanDivision, prop_quotRemAlt)
import System.Exit (exitFailure)
import Test.QuickCheck (quickCheck, verboseCheck, quickCheckResult, isSuccess)

main :: IO ()
main = do
  let tests =
        [ quickCheckResult prop_quotRemAltEuclideanDivision
        , quickCheckResult prop_quotRemAlt
        , quickCheckResult prop_divModSMTEuclideanDivision
        ]
  success <- fmap (all isSuccess) . sequence $ tests
  unless success exitFailure
