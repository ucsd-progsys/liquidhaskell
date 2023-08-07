{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Benchmark where

import Prelude hiding (readFile, writeFile, filter, zip, lookup)
import Data.String (fromString)
import Data.List as L
import Data.Vector as V hiding (length, concat, null, (++), last, find)
import qualified Data.Map.Strict as Map
import Data.ByteString.Char8 (unpack)
import Data.ByteString.Lazy.Char8 (readFile, writeFile)
import GHC.Generics (Generic)
import Data.Csv hiding (Options, Parser, lookup)

-- Individual entries

data Benchmark = Benchmark
  { test :: String
  , time :: Double
  } deriving stock (Eq, Ord, Show, Generic)

instance FromField Bool where
  parseField = pure . read . unpack

instance ToField Bool where
  toField b = fromString $ show b

instance FromNamedRecord Benchmark where
    parseNamedRecord m = Benchmark
                         <$> m .: "test"
                         <*> m .: "time"

instance ToNamedRecord Benchmark
instance DefaultOrdered Benchmark

readCSV :: FilePath -> IO (Vector Benchmark)
readCSV f = do bytes <- readFile f
               case decodeByName bytes of
                 Left err -> error err
                 Right (_, bs) -> pure bs

writeCSV :: FilePath -> [Benchmark] -> IO ()
writeCSV f dat = do
  let csvData = encodeDefaultOrderedByNameWith (defaultEncodeOptions { encUseCrLf = False }) dat
  writeFile f csvData

-- Data sets

type BData = Double

newtype BenchmarkComparison = BenchmarkComparison [(String, (BData, BData))]
  deriving stock (Eq, Ord, Show, Generic)

bdsLen :: BenchmarkComparison -> Int
bdsLen (BenchmarkComparison xs) = length xs

compareBenchmarks :: Vector Benchmark -> Vector Benchmark -> BenchmarkComparison
compareBenchmarks v1 v2 = BenchmarkComparison $ Map.toList $
    Map.unionWith (\(t0, _) (_, t1) -> (t0, t1))
      (Map.fromList [ (test b, (time b, 0)) | b <- V.toList v1])
      (Map.fromList [ (test b, (0, time b)) | b <- V.toList v2])

hiBenchmarks :: Int -> BenchmarkComparison -> BenchmarkComparison
hiBenchmarks n (BenchmarkComparison xs) =
    BenchmarkComparison $ L.take n $ sortOn (\(_, (bt, at)) -> at - bt) xs

loBenchmarks :: Int -> BenchmarkComparison -> BenchmarkComparison
loBenchmarks n (BenchmarkComparison xs) =
    BenchmarkComparison $ L.take n $ sortOn (\(_, (bt, at)) -> bt - at) xs
