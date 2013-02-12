-- | Replace a string by another string
--
-- Tested in this benchmark:
--
-- * Search and replace of a pattern in a text
--
module Benchmarks.Replace
    ( benchmark
    ) where

import Criterion (Benchmark, bgroup, bench, nf)
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Search as BL
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TL
import qualified Data.Text.Lazy.IO as TL

benchmark :: FilePath -> String -> String -> IO Benchmark
benchmark fp pat sub = do
    tl <- TL.readFile fp
    bl <- BL.readFile fp
    return $ bgroup "Replace"
        [ bench "LazyText"       $ nf (TL.length . TL.replace tpat tsub) tl
        , bench "LazyByteString" $ nf (BL.length . BL.replace bpat bsub) bl
        ]
  where
    tpat = TL.pack pat
    tsub = TL.pack sub
    bpat = B.concat $ BL.toChunks $ TL.encodeUtf8 tpat
    bsub = B.concat $ BL.toChunks $ TL.encodeUtf8 tsub
