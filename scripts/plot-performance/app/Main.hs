{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import Prelude hiding (readFile, filter, zip, lookup)
import Data.Maybe (isJust)
import Data.List (find, isPrefixOf)
import Data.Vector as V hiding (concat, null, (++), last, find)
import Options.Applicative
import System.Directory (createDirectoryIfMissing)

import Benchmark
import Plot (chartToFile)

data Options = Options
  { optsBeforeFile :: FilePath
  , optsAfterFile :: FilePath
  , optsCombine :: Bool
  , optsSort :: Maybe Int
  , optsFilter :: [String]
  , optsOutputDir :: Maybe FilePath
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
  <*> optional (strOption (long "outdir"
                           <> short 'o'
                           <> metavar "OUTDIR"
                           <> help "The folder which will receive output graphs."))

opts :: ParserInfo Options
opts = info (options <**> helper)
  (fullDesc
   <> progDesc "Plot test performance difference.")

main :: IO ()
main = do op <- execParser opts

          outdir <- maybe (pure "")
                          (\od -> do let nm = if null od || (not (null od) && (last od == '/')) then od else od ++ "/"
                                     createDirectoryIfMissing True nm
                                     pure nm)
                          (optsOutputDir op)

          -- TODO: use a regexp?
          let f = V.filter (\b -> isJust $ find (\fi -> fi `isPrefixOf` test b) (optsFilter op))

          vb <- f0 <$> readCSV (optsBeforeFile op)
          va <- f0 <$> readCSV (optsAfterFile op)

          case (optsSort op, null $ optsFilter op, optsCombine op) of
            (Just n , False, True ) ->
              let bdsf = splitBenchmarks (f vb) (f va)
                  hif = hiBenchmarks n bdsf
                  lof = loBenchmarks n bdsf
              in do chartToFile False "Top filtered speedups (seconds)" hif (outdir ++ "filtered-top.svg")
                    chartToFile True "Top filtered slowdowns (seconds)" lof (outdir ++ "filtered-bot.svg")
            (Just n , False, False) ->
              let bds = splitBenchmarks vb va
                  bdsf = splitBenchmarks (f vb) (f va)
                  hi = hiBenchmarks n bds
                  lo = loBenchmarks n bds
              in do chartToFile False ("Perf diff: " ++ show (optsFilter op) ++ " (seconds)") bdsf (outdir ++ "filtered.svg")
                    chartToFile False "Top speedups (seconds)" hi (outdir ++ "top.svg")
                    chartToFile True "Top slowdowns (seconds)" lo (outdir ++ "bot.svg")
            (Just n , True , _    ) ->
              let bds = splitBenchmarks vb va
                  hi = hiBenchmarks n bds
                  lo = loBenchmarks n bds
              in do chartToFile False "Top speedups (seconds)" hi (outdir ++ "top.svg")
                    chartToFile True "Top slowdowns (seconds)" lo (outdir ++ "bot.svg")
            (Nothing, False, _    ) ->
              let bdsf = splitBenchmarks (f vb) (f va)
              in chartToFile False "Perf diff (seconds)" bdsf (outdir ++ "filtered.svg")
            (Nothing, True , _    ) ->
              let bds = splitBenchmarks vb va
              in do chartToFile False "Perf" bds (outdir ++ "perf.svg")
  where
    f0 = V.filter (\b -> test b /= "app/Main")
