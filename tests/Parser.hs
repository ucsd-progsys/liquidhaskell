{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DoAndIfThenElse     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Simple test suite to test the parser.
--
-- Run as:
--
-- $ stack test :liquidhaskell-parser

module Main where

import           Data.Bifunctor
import qualified Language.Haskell.Liquid.Parse as LH
import qualified Language.Haskell.Liquid.Types as LH
import           Text.Parsec.Pos
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Runners.AntXML

-- ---------------------------------------------------------------------

-- | Test suite entry point, returns exit failure if any test fails.
main =  defaultMainWithIngredients (
                antXMLRunner:defaultIngredients
              ) tests

tests :: TestTree
tests =
  testGroup "Tests"
    [
      testSucceeds
    , testFails
    ]

testSucceeds :: TestTree
testSucceeds =
  testGroup "Should succeed"
    [ testCase "Int" $
       (parseSingleSpec "x :: Int") @?=
       (Right
          "Asrts ([\"x\" defined from: \"<test input>\" (line 1, column 1) to: \"<test input>\" (line 1, column 2)],(Int defined from: \"<test input>\" (line 1, column 6) to: \"<test input>\" (line 1, column 9),Nothing))")
    , testCase "k:Int -> Int" $
       (parseSingleSpec "x :: k:Int -> Int") @?=
       (Right
          "Asrts ([\"x\" defined from: \"<test input>\" (line 1, column 1) to: \"<test input>\" (line 1, column 2)],(k:Int -> Int defined from: \"<test input>\" (line 1, column 6) to: \"<test input>\" (line 1, column 18),Nothing))")
    ]

testFails :: TestTree
testFails =
  testGroup "Should fail"
    [ testCase "Maybe k:Int -> Int" $
       (bimap
          (unwords . words . show)
          show
          (parseSingleSpec "x :: Maybe k:Int -> Int")) @?=
       (Left
          "<test input>:1:13: Error: Cannot parse specification: Leftover while parsing")
    ]

-- ---------------------------------------------------------------------

-- | Parse a single type signature containing LH refinements. To be
-- used in the REPL.
parseSingleSpec
  :: String
  -> Either LH.Error String
parseSingleSpec = fmap show . (LH.singleSpecP (initialPos "<test input>"))
