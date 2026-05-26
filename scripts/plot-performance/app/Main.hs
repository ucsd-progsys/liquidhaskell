{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import Prelude hiding (readFile, filter, zip, lookup)
import Data.List (isPrefixOf)
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
  , optsAllocs :: Bool
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
  <*> switch (long "allocs"
              <> help "Compare allocations instead of time." )
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
          let isSelectedTest b = Prelude.any (`isPrefixOf` test b) (optsFilter op)
              selectTests = V.filter isSelectedTest
              dropAppMain = V.filter (\b -> test b /= "app/Main")
              dataSelector = if optsAllocs op then allocs else time
              mkTitle s = if optsAllocs op then s ++ " (MBs)" else s ++ " (seconds)"

          vb <- dropAppMain <$> readCSV (optsBeforeFile op)
          va <- dropAppMain <$> readCSV (optsAfterFile op)

          case (optsSort op, null $ optsFilter op, optsCombine op) of
            (Just n , False, True ) ->
              let bdsf = compareBenchmarks (selectTests vb) (selectTests va)
                  hif = hiBenchmarks dataSelector n bdsf
                  lof = loBenchmarks dataSelector n bdsf
              in do chartToFile (mkTitle "Top filtered speedups") dataSelector hif (outdir ++ "filtered-top.svg")
                    chartToFile (mkTitle "Top filtered slowdowns") dataSelector lof (outdir ++ "filtered-bot.svg")
            (Just n , False, False) ->
              let bds = compareBenchmarks vb va
                  bdsf = compareBenchmarks (selectTests vb) (selectTests va)
                  hi = hiBenchmarks dataSelector n bds
                  lo = loBenchmarks dataSelector n bds
              in do chartToFile (mkTitle $ "Perf diff: " ++ show (optsFilter op)) dataSelector bdsf (outdir ++ "filtered.svg")
                    chartToFile (mkTitle "Top speedups") dataSelector hi (outdir ++ "top.svg")
                    chartToFile (mkTitle "Top slowdowns") dataSelector lo (outdir ++ "bot.svg")
            (Just n , True , _    ) ->
              let bds = compareBenchmarks vb va
                  hi = hiBenchmarks dataSelector n bds
                  lo = loBenchmarks dataSelector n bds
              in do chartToFile (mkTitle "Top speedups") dataSelector hi (outdir ++ "top.svg")
                    chartToFile (mkTitle "Top slowdowns") dataSelector lo (outdir ++ "bot.svg")
            (Nothing, False, _    ) ->
              let bdsf = compareBenchmarks (selectTests vb) (selectTests va)
              in chartToFile (mkTitle "Perf diff") dataSelector bdsf (outdir ++ "filtered.svg")
            (Nothing, True , _    ) ->
              let bds = compareBenchmarks vb va
              in do chartToFile "Perf" dataSelector bds (outdir ++ "perf.svg")
