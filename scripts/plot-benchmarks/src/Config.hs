{-# LANGUAGE DeriveDataTypeable #-}

module Config where

import System.Console.CmdArgs
import System.Directory

data OutputType =
   Svg
   | Csv
     deriving (Eq, Data, Typeable, Show)

data Config =
   Config { logDir :: FilePath,
            outputDir :: FilePath,
            outputType :: OutputType,
            plotCompare :: [(String, String)],
            plot :: [String]
          } deriving (Eq, Data, Typeable, Show)

pwd :: FilePath
pwd = "."

instance Default Config where
   def = Config { logDir = pwd,
                  outputDir = pwd,
                  outputType = Csv,
                  plotCompare = def,
                  plot = def
                }

config :: Config
config = Config
            { logDir = pwd &= help "The directory that contains the logs",
              outputDir = pwd &= help "The diretory to output graphs to",
              outputType = Csv &= help "The type of output to produce",
              plotCompare = def &= help "Pairs of benchmarks to compare",
              plot = def &= help "Benchmarks to plot"
            }
            &= program "plot-benchmarks"
            &= summary ("plot-benchmarks - Copyright 2016 Regents of"
                        ++ "the University of California.")
            &= details ["Plot LiquidHaskell benchmarks over time"]

getConfig :: IO Config
getConfig = do
   conf <- cmdArgs config
   ld <- makeAbsolute $ logDir conf
   od <- makeAbsolute $ outputDir conf
   return $ conf {logDir = ld, outputDir = od}
