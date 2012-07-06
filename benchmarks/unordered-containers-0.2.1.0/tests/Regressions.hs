module Main where

import qualified Data.HashMap.Strict as HM
import Data.Maybe
import Test.HUnit (Assertion, assert)
import Test.Framework (Test, defaultMain)
import Test.Framework.Providers.HUnit (testCase)

issue32 :: Assertion
issue32 = assert $ isJust $ HM.lookup 7 m'
  where
    ns = [0..16] :: [Int]
    m = HM.fromList (zip ns (repeat []))    
    m' = HM.delete 10 m

------------------------------------------------------------------------
-- * Test list

tests :: [Test]
tests =
    [
      testCase "issue32" issue32
    ]

------------------------------------------------------------------------
-- * Test harness

main :: IO ()
main = defaultMain tests
