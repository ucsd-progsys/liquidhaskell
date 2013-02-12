-- | Regression tests for specific bugs.
--
{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
module Tests.Regressions
    (
      tests
    ) where

import Control.Exception (SomeException, handle)
import System.IO
import Test.HUnit (assertFailure)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as LB
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Encoding as LE
import qualified Test.Framework as F
import qualified Test.Framework.Providers.HUnit as F

import Tests.Utils (withTempFile)

-- Reported by Michael Snoyman: UTF-8 encoding a large lazy bytestring
-- caused either a segfault or attempt to allocate a negative number
-- of bytes.
lazy_encode_crash :: IO ()
lazy_encode_crash = withTempFile $ \ _ h ->
   LB.hPut h . LE.encodeUtf8 . LT.pack . replicate 100000 $ 'a'

-- Reported by Pieter Laeremans: attempting to read an incorrectly
-- encoded file can result in a crash in the RTS (i.e. not merely an
-- exception).
hGetContents_crash :: IO ()
hGetContents_crash = withTempFile $ \ path h -> do
  B.hPut h (B.pack [0x78, 0xc4 ,0x0a]) >> hClose h
  h' <- openFile path ReadMode
  hSetEncoding h' utf8
  handle (\(_::SomeException) -> return ()) $
    T.hGetContents h' >> assertFailure "T.hGetContents should crash"

-- Reported by Ian Lynagh: attempting to allocate a sufficiently large
-- string (via either Array.new or Text.replicate) could result in an
-- integer overflow.
replicate_crash :: IO ()
replicate_crash = handle (\(_::SomeException) -> return ()) $
                  T.replicate (2^power) "0123456789abcdef" `seq`
                  assertFailure "T.replicate should crash"
  where
    power | maxBound == (2147483647::Int) = 28
          | otherwise                     = 60 :: Int

tests :: F.Test
tests = F.testGroup "Regressions"
    [ F.testCase "hGetContents_crash" hGetContents_crash
    , F.testCase "lazy_encode_crash" lazy_encode_crash
    , F.testCase "replicate_crash" replicate_crash
    ]
