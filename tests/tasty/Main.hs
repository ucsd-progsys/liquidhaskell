module Main where

import Test.Tasty
import ErrorFilterReportTests

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests"
        errorFilterReportTests
