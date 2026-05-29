{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Benchmark where

import Prelude hiding (readFile, writeFile, filter, zip, lookup)
import Data.String (fromString)
import Data.List as L
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.Map.Strict as Map
import Data.ByteString.Char8 (unpack)
import Data.ByteString.Lazy.Char8 (readFile, writeFile)
import GHC.Generics (Generic)
import Data.Csv hiding (Options, Parser, lookup)

-- Individual entries

-- | A single benchmark entry
data Benchmark = Benchmark
  { test :: String   -- ^ test name
  , time :: Double   -- ^ time in seconds
  , allocs :: Double -- ^ allocations in MBs
  , result :: Bool   -- ^ whether the test passed or failed
  } deriving stock (Eq, Ord, Show, Generic)

zeroBenchmark :: Benchmark -> Benchmark
zeroBenchmark b = b { time = 0, allocs = 0 }

instance FromField Bool where
  parseField = pure . read . unpack

instance ToField Bool where
  toField b = fromString $ show b

instance FromNamedRecord Benchmark where
    parseNamedRecord m = Benchmark
                         <$> m .: "test"
                         <*> m .: "time"
                         <*> m .: "allocs"
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

data BenchmarkWarning
    = MissingMeasureAfter
    | MissingMeasureBefore
    | FailedRunAfter
    | FailedRunBefore

data BenchmarkComparison = BenchmarkComparison
    { -- | Warnings for tests with the given labels
      bcWarnings :: [(String, BenchmarkWarning)]
      -- | Data of benchmars present in both sets
    , bcCombined :: [(Benchmark, Benchmark)]
    }

bcLen :: BenchmarkComparison -> Int
bcLen bc = length (bcCombined bc) + warningsLength bc
  where
    warningsLength :: BenchmarkComparison -> Int
    warningsLength = length . bcWarnings

compareBenchmarks :: Vector Benchmark -> Vector Benchmark -> BenchmarkComparison
compareBenchmarks v1 v2 = BenchmarkComparison
    { bcWarnings = Map.toList $ Map.unions
        [ Map.fromList [ (test b, FailedRunBefore) | b <- V.toList failedBefore ]
        , Map.fromList [ (test b, FailedRunAfter) | b <- V.toList failedAfter ]
        , Map.map (const MissingMeasureBefore) (Map.difference after before)
        , Map.map (const MissingMeasureAfter) (Map.difference before after)
        ]
    , bcCombined = Map.elems $ Map.unionWith (\(a, _) (_, b) -> (a, b)) before after
    }
  where
    (vBefore, failedBefore) = V.partition result v1
    (vAfter, failedAfter) = V.partition result v2
    before = Map.fromList [ (test b, (b, zeroBenchmark b)) | b <- V.toList vBefore]
    after = Map.fromList [ (test b, (zeroBenchmark b, b)) | b <- V.toList vAfter]

-- | Sort the benchmarks by the difference in the given field, and take the top
-- N (after removing warnings)
hiBenchmarks :: (Benchmark -> Double) -> Int -> BenchmarkComparison -> BenchmarkComparison
hiBenchmarks f n bc =
    bc { bcCombined =
           L.take n
           $ sortOn (\(bt, at) -> (f at - f bt) / f bt)
           $ filter
               (\(bt, _) -> test bt `notElem` map fst (bcWarnings bc))
               (bcCombined bc)
       }

-- | Sort the benchmarks by the difference in the given field, and take the bottom
-- N (after removing warnings)
loBenchmarks :: (Benchmark -> Double) -> Int -> BenchmarkComparison -> BenchmarkComparison
loBenchmarks f n bc =
    bc { bcCombined =
           L.take n
           $ sortOn (\(bt, at) -> (f bt - f at) / f bt)
           $ filter
               (\(bt, _) -> test bt `notElem` map fst (bcWarnings bc))
               (bcCombined bc)
       }
