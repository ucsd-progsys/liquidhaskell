-- | Simple test suite to test the parser.
--
-- Run as:
--
-- $ stack test :liquidhaskell-parser

module Main where

import           Data.Bifunctor
import qualified Language.Haskell.Liquid.Parse as LH
import qualified Language.Haskell.Liquid.Types as LH
import           Test.Hspec
import           Text.Parsec.Pos

-- | Test suite entry point, returns exit failure if any test fails.
main :: IO ()
main = hspec spec

-- | Test suite.
spec :: Spec
spec = do
  describe "Should succeed" succeeds
  describe "Should fail" fails

-- | Tests for the parser.
succeeds :: Spec
succeeds = do
  it
    "Int"
    (shouldBe
       (parseSingleSpec "x :: Int")
       (Right
          "Asrts ([\"x\" defined from: \"<test input>\" (line 1, column 1) to: \"<test input>\" (line 1, column 2)],(Int defined from: \"<test input>\" (line 1, column 6) to: \"<test input>\" (line 1, column 9),Nothing))"))
  it
    "k:Int -> Int"
    (shouldBe
       (parseSingleSpec "x :: k:Int -> Int")
       (Right
          "Asrts ([\"x\" defined from: \"<test input>\" (line 1, column 1) to: \"<test input>\" (line 1, column 2)],(k:Int -> Int defined from: \"<test input>\" (line 1, column 6) to: \"<test input>\" (line 1, column 18),Nothing))"))

fails :: Spec
fails = do
  it
    "Maybe k:Int -> Int"
    (shouldBe
       (bimap
          (unwords . words . show)
          show
          (parseSingleSpec "x :: Maybe k:Int -> Int"))
       (Left
          "<test input>:1:13: Error: Cannot parse specification: Leftover while parsing"))

-- | Parse a single type signature containing LH refinements. To be
-- used in the REPL.
parseSingleSpec
  :: String
  -> Either LH.Error String
parseSingleSpec = fmap show . (LH.singleSpecP (initialPos "<test input>"))
