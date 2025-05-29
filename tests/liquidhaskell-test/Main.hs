module Main where

import Test.Tasty
import qualified QuotRem (tests)

main :: IO ()
main = defaultMain QuotRem.tests
