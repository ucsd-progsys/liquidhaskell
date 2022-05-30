{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Monad (guard)
import Data.String (fromString)
import Prelude hiding (writeFile)
import Data.Csv hiding (Options, Parser)
import Data.Aeson hiding (Options)
import GHC.Generics (Generic)
import Options.Applicative
import Data.Traversable (for)
import Data.Maybe (catMaybes)

import Data.ByteString.Lazy (ByteString)
import Data.ByteString.Lazy.Char8 (writeFile)

data Phase = Phase
  { phaseTime :: Double
  , phaseName :: String
  , phaseModule :: String
  , phaseAlloc :: Int
  } deriving stock (Eq, Ord, Show, Generic)

instance FromJSON Phase

data PhasesSummary = PhasesSummary
  { test :: String
  , time :: Double
  , result :: Bool
  } deriving stock (Eq, Ord, Show, Generic)

instance ToField Bool where
  toField b = fromString $ show b

instance ToNamedRecord PhasesSummary
instance DefaultOrdered PhasesSummary

data Options = Options
  { optsFilesToParse :: [FilePath]
  , optsPhasesToCount :: [String]
  , optsOutputFile :: FilePath
  } deriving stock (Eq, Ord, Show)

options :: Parser Options
options = Options <$>
  (many (argument
         str
          (metavar "FILEPATH..."
           <> help "The files you wish to process.")))
  <*> (many (strOption (long "phase"
                        <> short 'p'
                        <> metavar "PHASE"
                        <> help "Phase to include in summary.  Can be specified more thance once.")))
  <*> (strOption (long "output"
                  <> short 'o'
                  <> metavar "OUTPUTFILEPATH"
                  <> help "File to which to output CSV contents."))

opts :: ParserInfo Options
opts = info (options <**> helper)
  (fullDesc
   <> progDesc "Summarize timing info.")

program :: Options -> IO ()
program Options {..} = do
  csvFields <- for optsFilesToParse $ \fp -> do
    Just (phases :: [Phase]) <- decodeFileStrict' fp
    let (modName, time) = foldr (\Phase {..} (_, acc) -> (phaseModule,
                                                          if init phaseName `elem` optsPhasesToCount then acc + phaseTime else acc)) ("", 0) phases
     -- convert milliseconds -> seconds
    if modName == "" then pure Nothing else pure $ Just $ PhasesSummary modName (time / 1000) True
  let csvData = encodeDefaultOrderedByNameWith (defaultEncodeOptions { encUseCrLf = False }) $ catMaybes csvFields
  writeFile optsOutputFile csvData

main :: IO ()
main = program =<< execParser opts
