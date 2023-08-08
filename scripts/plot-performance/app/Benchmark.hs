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

data BenchmarkWarning
    = MissingMeasureAfter
    | MissingMeasureBefore
    | FailedRunAfter
    | FailedRunBefore

data BenchmarkComparison = BenchmarkComparison
    { -- | Warnings for tests with the given labels
      bcWarnings :: [(String, BenchmarkWarning)]
      -- | Data of benchmars present in both sets
    , bcCombined :: [(String, (BData, BData))]
    }

bcLen :: BenchmarkComparison -> Int
bcLen bc = length (bcCombined bc) + warningsLength bc

warningsLength :: BenchmarkComparison -> Int
warningsLength bc = length (bcWarnings bc)

compareBenchmarks :: Vector Benchmark -> Vector Benchmark -> BenchmarkComparison
compareBenchmarks v1 v2 = BenchmarkComparison
    { bcWarnings = Map.toList $ Map.unions
        [ Map.fromList [ (test b, FailedRunBefore) | b <- V.toList failedBefore ]
        , Map.fromList [ (test b, FailedRunAfter) | b <- V.toList failedAfter ]
        , Map.map (const MissingMeasureBefore) (Map.difference after before)
        , Map.map (const MissingMeasureAfter) (Map.difference before after)
        ]
    , bcCombined = Map.toList $
        Map.unionWith (\(t0, _) (_, t1) -> (t0, t1)) before after
    }
  where
    (vBefore, failedBefore) = V.partition result v1
    (vAfter, failedAfter) = V.partition result v2
    before = Map.fromList [ (test b, (time b, 0)) | b <- V.toList vBefore]
    after = Map.fromList [ (test b, (0, time b)) | b <- V.toList vAfter]

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
