-- | Benchmarks simple file reading
--
-- Tested in this benchmark:
--
-- * Reading a file from the disk
--
module Benchmarks.FileRead
    ( benchmark
    ) where

import Control.Exception (evaluate)
import Criterion (Benchmark, bgroup, bench)
import qualified Data.ByteString as SB
import qualified Data.ByteString.Lazy as LB
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.IO as T
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Encoding as LT
import qualified Data.Text.Lazy.IO as LT

benchmark :: FilePath -> IO Benchmark
benchmark p = return $ bgroup "FileRead"
    [ bench "String" $ readFile p >>= evaluate . length
    , bench "ByteString" $ SB.readFile p >>= evaluate . SB.length
    , bench "LazyByteString" $ LB.readFile p >>= evaluate . LB.length
    , bench "Text" $ T.readFile p >>= evaluate . T.length
    , bench "LazyText" $ LT.readFile p >>= evaluate . LT.length
    , bench "TextByteString" $
        SB.readFile p >>= evaluate . T.length . T.decodeUtf8
    , bench "LazyTextByteString" $
        LB.readFile p >>= evaluate . LT.length . LT.decodeUtf8
    ]
