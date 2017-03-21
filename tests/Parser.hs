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
import           Data.Data
import           Data.Generics.Aliases
import           Data.Generics.Schemes
import           Language.Fixpoint.Types.Spans
import qualified Language.Haskell.Liquid.Parse as LH
import qualified Language.Haskell.Liquid.Types as LH
import           Text.Parsec.Pos
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Runners.AntXML

-- ---------------------------------------------------------------------

-- | Test suite entry point, returns exit failure if any test fails.
main :: IO ()
main =  defaultMainWithIngredients (
                antXMLRunner:defaultIngredients
              ) tests

tests :: TestTree
tests =
  testGroup "Tests"
    [
      testSucceeds
    , testFails
    , testSpecP
    ]

-- ---------------------------------------------------------------------

-- Test that the top level production works, each of the sub-elements will be tested separately
testSpecP :: TestTree
testSpecP =
  testGroup "specP"
    [ testCase "assume" $
       parseSingleSpec "assume foo :: a -> a " @?=
          "Assm (\"foo\" (dummyLoc),lq_tmp$db##0:a -> a (dummyLoc))"

    , testCase "assert" $
       parseSingleSpec "assert myabs :: Int -> PosInt" @?=
          "Asrt (\"myabs\" (dummyLoc),lq_tmp$db##0:Int -> PosInt (dummyLoc))"
    ]

-- ---------------------------------------------------------------------

testSucceeds :: TestTree
testSucceeds =
  testGroup "Should succeed"
    [ testCase "Int" $
       (parseSingleSpec "x :: Int") @?=
          "Asrts ([\"x\" (dummyLoc)],(Int (dummyLoc),Nothing))"

    , testCase "k:Int -> Int" $
       (parseSingleSpec "x :: k:Int -> Int") @?=
          "Asrts ([\"x\" (dummyLoc)],(k:Int -> Int (dummyLoc),Nothing))"
    ]

-- ---------------------------------------------------------------------

testFails :: TestTree
testFails =
  testGroup "Should fail"
    [ testCase "Maybe k:Int -> Int" $
          parseSingleSpec "x :: Maybe k:Int -> Int" @?=
            "<test>:1:13: Error: Cannot parse specification:\n    Leftover while parsing"
    ]

-- ---------------------------------------------------------------------

-- | Parse a single type signature containing LH refinements. To be
-- used in the REPL.
parseSingleSpec :: String -> String
parseSingleSpec src =
  case LH.singleSpecP (initialPos "<test>") src of
    Left err  -> show err
    Right res -> show $ dummyLocs res

-- ---------------------------------------------------------------------

dummyLocs :: (Data a) => a -> a
dummyLocs = everywhere (mkT posToDummy)
  where
    posToDummy :: SourcePos -> SourcePos
    posToDummy _ = dummyPos "Fixpoint.Types.dummyLoc"
