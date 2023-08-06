{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Benchmark where

import Prelude hiding (readFile, writeFile, filter, zip, lookup)
import Data.Ord (Down(..))
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

type BData = (Double, Bool)

data BenchmarkDataSet = BenchmarkDS
  { removed :: [(String, BData)]
  , combined :: [(String, BData, BData)]
  , added :: [(String, BData)]
  } deriving stock (Eq, Ord, Show, Generic)

bdsLen :: BenchmarkDataSet -> Int
bdsLen (BenchmarkDS rs xs as) = length rs + length xs + length as

splitBenchmarks :: Vector Benchmark
                -> Vector Benchmark
                -> BenchmarkDataSet
splitBenchmarks v1 v2 = go v1 (M.fromList $ V.toList $ V.map kvfun v2)
  where
  kvfun b = (test b, (time b, result b))
  go :: Vector Benchmark -> Map String BData -> BenchmarkDataSet
  go vb ma = case V.uncons vb of
               Just (Benchmark n f r, tl) ->
                 case M.lookup n ma of
                   Just a  -> let (BenchmarkDS rs xs as) = go tl (M.delete n ma) in
                              BenchmarkDS rs ((n, (f, r), a) : xs) as
                   Nothing -> let (BenchmarkDS rs xs as) = go tl ma in
                              BenchmarkDS ((n, (f, r)) : rs) xs as
               Nothing -> BenchmarkDS [] [] (M.toList ma)

hiBenchmarks :: Int -> BenchmarkDataSet -> BenchmarkDataSet
hiBenchmarks n (BenchmarkDS rs xs as) =
  let rs' = L.take n $ sortOn (Down . fst . snd) rs
      ys = sortOn (\(_, bt, at) -> fst at - fst bt) xs
      ys' = L.take (n - length rs') ys
      as' = L.take (n - (length rs' + length ys')) $ sortOn (Down . fst . snd) as
  in BenchmarkDS rs' ys' as'

loBenchmarks :: Int -> BenchmarkDataSet -> BenchmarkDataSet
loBenchmarks n (BenchmarkDS rs xs as) =
  let as' = L.take n $ sortOn (fst . snd) as
      ys = sortOn (\(_, bt, at) -> fst bt - fst at) xs
      ys' = L.take (n - length as') ys
      rs' = L.take (n - (length as' + length ys')) $ sortOn (fst . snd) rs
  in BenchmarkDS rs' ys' as'
