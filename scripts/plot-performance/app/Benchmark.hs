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
import Data.Map as M hiding (null)
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

newtype BenchmarkDataSet = BenchmarkDS [(String, BData, BData)]
  deriving stock (Eq, Ord, Show, Generic)

bdsLen :: BenchmarkDataSet -> Int
bdsLen (BenchmarkDS xs) = length xs

compareBenchmarks :: Vector Benchmark -> Vector Benchmark -> BenchmarkDataSet
compareBenchmarks v1 v2 = go v1 (M.fromList $ V.toList $ V.map kvfun v2)
  where
  kvfun b = (test b, time b)
  go :: Vector Benchmark -> Map String BData -> BenchmarkDataSet
  go vb ma = case V.uncons vb of
               Just (Benchmark n f, tl) ->
                 case M.lookup n ma of
                   Just a  -> let BenchmarkDS xs = go tl (M.delete n ma) in
                              BenchmarkDS ((n, f, a) : xs)
                   Nothing -> let BenchmarkDS xs = go tl ma in
                              BenchmarkDS ((n, f, 0) : xs)
               Nothing -> BenchmarkDS [ (n, 0, f) | (n, f) <- M.toList ma ]

hiBenchmarks :: Int -> BenchmarkDataSet -> BenchmarkDataSet
hiBenchmarks n (BenchmarkDS xs) = BenchmarkDS $ L.take n $ sortOn (\(_, bt, at) -> at - bt) xs

loBenchmarks :: Int -> BenchmarkDataSet -> BenchmarkDataSet
loBenchmarks n (BenchmarkDS xs) = BenchmarkDS $ L.take n $ sortOn (\(_, bt, at) -> bt - at) xs
