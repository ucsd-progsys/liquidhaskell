-- | Testing the internal builder monoid
--
-- Tested in this benchmark:
--
-- * Concatenating many small strings using a builder
--
{-# LANGUAGE OverloadedStrings #-}
module Benchmarks.Builder
    ( benchmark
    ) where

import Criterion (Benchmark, bgroup, bench, nf)
import Data.Binary.Builder as B
import Data.ByteString.Char8 ()
import Data.Monoid (mconcat)
import qualified Blaze.ByteString.Builder as Blaze
import qualified Blaze.ByteString.Builder.Char.Utf8 as Blaze
import qualified Data.ByteString as SB
import qualified Data.ByteString.Lazy as LB
import qualified Data.Text as T
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Builder as LTB

benchmark :: IO Benchmark
benchmark = return $ bgroup "Builder"
    [ bench "LazyText" $ nf
        (LT.length . LTB.toLazyText . mconcat . map LTB.fromText) texts
    , bench "Binary" $ nf
        (LB.length . B.toLazyByteString . mconcat . map B.fromByteString)
        byteStrings
    , bench "Blaze" $ nf
        (LB.length . Blaze.toLazyByteString . mconcat . map Blaze.fromString)
        strings
    ]

texts :: [T.Text]
texts = take 200000 $ cycle ["foo", "λx", "由の"]
{-# NOINLINE texts #-}

-- Note that the non-ascii characters will be chopped
byteStrings :: [SB.ByteString]
byteStrings = take 200000 $ cycle ["foo", "λx", "由の"]
{-# NOINLINE byteStrings #-}

-- Note that the non-ascii characters will be chopped
strings :: [String]
strings = take 200000 $ cycle ["foo", "λx", "由の"]
{-# NOINLINE strings #-}
