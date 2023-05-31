{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
--{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import Prelude hiding (readFile, filter, zip, lookup)
import Data.Vector as V hiding (concat)
import Data.Map as M
import Options.Applicative

import Benchmark
--import Plot

data Options = Options
  { optsBeforeFile :: FilePath
  , optsAfterFile :: FilePath
  , optsCombine :: Bool
  , optsSort :: Maybe Int
  , optsFilter :: [String]
  , optsOutputDir :: FilePath
  } deriving stock (Eq, Ord, Show)

options :: Parser Options
options = Options <$>
      strOption (long "before"
                  <> short 'b'
                  <> metavar "BEFOREPATH"
                  <> help "Input CSV file with original benchmark data.")
  <*> strOption (long "after"
                  <> short 'a'
                  <> metavar "AFTERPATH"
                  <> help "Input CSV file with modified benchmark data.")
  <*> switch (long "combine"
              <> short 'c'
              <> help "If both sort and filter are used, combine their actions instead of doing both in parallel (default)" )
  <*> optional (option auto (long "sort"
                  <> short 's'
                  <> metavar "N"
                  <> help "Generate two graphs for top and bottom N differences."))
  <*> (concat <$> many (option (words <$> str) (long "filter"
                                                 <> short 'f'
                                                 <> metavar "FILTER"
                                                 <> help "Whitespace-separated list of test names to include, in quotes.")))
  <*> strOption (long "outdir"
                  <> short 'o'
                  <> metavar "OUTDIR"
                  <> help "The folder which will receive output graphs.")

opts :: ParserInfo Options
opts = info (options <**> helper)
  (fullDesc
   <> progDesc "Plot test performance difference.")

splitBenchmarks :: Vector Benchmark
                -> Vector Benchmark
                -> BenchmarkDataSet
splitBenchmarks v1 v2 = go v1 (M.fromList $ V.toList $ V.map kvfun v2)
  where
  kvfun b =
    let t = time b in
    (test b, if result b then Right t else Left t)
  go :: Vector Benchmark -> Map String BData -> BenchmarkDataSet
  go vb ma = case V.uncons vb of
               Just (Benchmark n f r, tl) ->
                 case M.lookup n ma of
                   Just a -> let (BenchmarkDS rs xs as) = go tl (M.delete n ma) in
                             BenchmarkDS rs ((n, if r then Right f else Left f, a) : xs) as
                   Nothing -> let (BenchmarkDS rs xs as) = go tl ma in
                              BenchmarkDS ((n, if r then Right f else Left f) : rs) xs as
               Nothing -> BenchmarkDS [] [] (M.toList ma)

main :: IO ()
main = do op <- execParser opts
          --let filt = optsFilter op
          let ffilt1 = V.filter (\b -> test b /= "app/Main")
          --let ffilt = if null filt
          --              then id
          --              -- TODO: use something more sophisticated (regexp)?
          --              else filter (\b -> isJust $ find (\f -> f `isPrefixOf` test b) filt)

          vb <- ffilt1 <$> readCSV (optsBeforeFile op)
          va <- ffilt1 <$> readCSV (optsAfterFile op)

          case (optSort, optsFilter, optsCombine) of
            (True, Just n, _:_) ->
            (True, Just n, _:_) ->

          --let vba = zip vb va
          --_ <- main1
          --pure ()
          let bds = splitBenchmarks vb va
          let (hi1,hi2) = decouple (hiBenchmarks 50 bds) False
          let (lo1,lo2) = decouple (loBenchmarks 50 bds) True
          writeCSV (o ++ "/before-hi.csv") hi1
          writeCSV (o ++ "/before-lo.csv") lo1
          writeCSV (o ++ "/after-hi.csv") hi2
          writeCSV (o ++ "/after-lo.csv") lo2
