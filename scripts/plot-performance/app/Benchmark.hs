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
  , result :: Bool
  } deriving stock (Eq, Ord, Show, Generic)

instance FromField Bool where
  parseField = pure . read . unpack

instance ToField Bool where
  toField b = fromString $ show b

instance FromNamedRecord Benchmark where
    parseNamedRecord m = Benchmark
                         <$> m .: "test"
                         <*> m .: "time"
                         <*> m .: "result"

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

data BenchmarkComparison = BenchmarkComparison
    { -- | Labels of benchmarks only present in the "before" set
      bcOnlyBefore :: [String]
      -- | Labels of benchmarks only present in the "after" set
    , bcOnlyAfter :: [String]
      -- | Labels of benchmarks that failed
    , bcFailed :: [String]
      -- | Data of benchmars present in both sets
    , bcCombined :: [(String, (BData, BData))]
    }
  deriving stock (Eq, Ord, Show, Generic)

bdsLen :: BenchmarkComparison -> Int
bdsLen bc = length (bcCombined bc) + warningsLength bc

warningsLength :: BenchmarkComparison -> Int
warningsLength bc =
  length (bcOnlyBefore bc) + length (bcOnlyAfter bc) + length (bcFailed bc)

compareBenchmarks :: Vector Benchmark -> Vector Benchmark -> BenchmarkComparison
compareBenchmarks v1 v2 = BenchmarkComparison
    { bcOnlyBefore = Map.keys (Map.difference before after) \\ failed
    , bcOnlyAfter = Map.keys (Map.difference after before) \\ failed
    , bcFailed = failed
    , bcCombined = Map.toList $
        Map.unionWith (\(t0, _) (_, t1) -> (t0, t1)) before after
    }
  where
    (vBefore, failedBefore) = V.partition result v1
    (vAfter, failedAfter) = V.partition result v2
    before = Map.fromList [ (test b, (time b, 0)) | b <- V.toList vBefore]
    after = Map.fromList [ (test b, (0, time b)) | b <- V.toList vAfter]
    failed = Prelude.map test $ nub $ V.toList $ failedBefore <> failedAfter

hiBenchmarks :: Int -> BenchmarkComparison -> BenchmarkComparison
hiBenchmarks n bc =
    bc { bcCombined =
           L.take (n - warningsLength bc) $ sortOn (\(_, (bt, at)) -> at - bt) (bcCombined bc)
       }

loBenchmarks :: Int -> BenchmarkComparison -> BenchmarkComparison
loBenchmarks n bc =
    bc { bcCombined =
           L.take (n - warningsLength bc) $ sortOn (\(_, (bt, at)) -> bt - at) (bcCombined bc)
       }
