{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
--{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Benchmark where

import Prelude hiding (readFile, writeFile, filter, zip, lookup)
import Data.Ord (Down(..))
import Data.Either.Extra (fromEither, isRight)
import Data.String (fromString)
import Data.List as L
import Data.Vector (Vector)
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

type BData = Either Double Double

data BenchmarkDataSet = BenchmarkDS
  { removed :: [(String, BData)]
  , combined :: [(String, BData, BData)]
  , added :: [(String, BData)]
  } deriving stock (Eq, Ord, Show, Generic)

hiBenchmarks :: Int -> BenchmarkDataSet -> BenchmarkDataSet
hiBenchmarks n (BenchmarkDS rs xs as) =
  let rs' = L.take n $ sortOn (Down . fromEither . snd) rs
      ys = sortOn (\(_, bt, at) -> fromEither at - fromEither bt) xs
      ys' = L.take (n - L.length rs') ys
      as' = L.take (n - (L.length rs' + L.length ys')) $ sortOn (Down . fromEither . snd) as
  in BenchmarkDS rs' ys' as'

loBenchmarks :: Int -> BenchmarkDataSet -> BenchmarkDataSet
loBenchmarks n (BenchmarkDS rs xs as) =
  let as' = L.take n $ sortOn (fromEither . snd) as
      ys = sortOn (\(_, bt, at) -> fromEither bt - fromEither at) xs
      ys' = L.take (n - L.length as') ys
      rs' = L.take (n - (L.length as' + L.length ys')) $ sortOn (fromEither . snd) rs
  in BenchmarkDS rs' ys' as'

decouple :: BenchmarkDataSet -> Bool -> ([Benchmark], [Benchmark])
decouple (BenchmarkDS rs xs as) rev =
  let
    rb = L.map toBench1 rs
    (xs1,xs2) = L.unzip $ L.map toBench2 xs
    ab = L.map toBench1 as
  in
  if rev
    then (L.map nullBench ab ++ xs1 ++ rb, ab ++ xs2 ++ L.map nullBench rb)
    else (rb ++ xs1 ++ L.map nullBench ab, L.map nullBench rb ++ xs2 ++ ab)
  where
    toBench1 (n, bd) = Benchmark n (fromEither bd) (isRight bd)
    toBench2 (n, bd1, bd2) = (Benchmark n (fromEither bd1) (isRight bd1), Benchmark n (fromEither bd2) (isRight bd2))
    nullBench (Benchmark n _ _) = Benchmark n 0.0 False
