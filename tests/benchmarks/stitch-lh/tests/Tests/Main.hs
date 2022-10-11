-- Main testing module

module Main where

import Test.Tasty

import Tests.Lex
import Tests.Parse
import Tests.Check

allTests :: TestTree
allTests = testGroup "Top" [lexTests, parseTests, checkTests]

main :: IO ()
main = defaultMain allTests
