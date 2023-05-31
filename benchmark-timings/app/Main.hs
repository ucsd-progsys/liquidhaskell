{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import Data.String (fromString)
import Prelude hiding (writeFile)
import Data.Csv hiding (Options, Parser)
import Data.Aeson hiding (Options)
import GHC.Generics (Generic)
import Options.Applicative
import Data.Traversable (for)
import Data.Maybe (catMaybes)

import Data.ByteString.Lazy.Char8 (writeFile)
import Data.List (foldl', intersperse, isSuffixOf)
import qualified Text.ParserCombinators.ReadP as ReadP

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
  many (argument
         str
          (metavar "FILEPATH..."
           <> help "The files you wish to process."))
  <*> many (strOption (long "phase"
                        <> short 'p'
                        <> metavar "PHASE"
                        <> help "Phase to include in summary.  Can be specified more thance once."))
  <*> strOption (long "output"
                  <> short 'o'
                  <> metavar "OUTPUTFILEPATH"
                  <> help "File to which to output CSV contents.")

opts :: ParserInfo Options
opts = info (options <**> helper)
  (fullDesc
   <> progDesc "Summarize timing info.")

-- | Parse the original filename from the .dump-timings filename
dumpFilenameParser :: ReadP.ReadP FilePath
dumpFilenameParser = do
  pathPieces <- ReadP.sepBy (ReadP.many ReadP.get) (ReadP.string "--")
  _ <- ReadP.string ".dump-timings.json"
  rest <- case pathPieces of
    _arch : _ghcVersion : _pkg : _ : p : rest | isSuffixOf "-tmp" p ->
      pure rest
    _arch : _ghcVersion : _pkg : rest ->
      pure rest
    _ ->
      ReadP.pfail
  ReadP.eof
  pure . mconcat $ intersperse "/" rest

program :: Options -> IO ()
program Options {..} = do
  csvFields <- for optsFilesToParse $ \fp ->
    case ReadP.readP_to_S dumpFilenameParser fp of
      (originalFilename, _):_ -> do
        Just (phases :: [Phase]) <- decodeFileStrict' fp
        let time = foldl' (+) 0 [ phaseTime p | p <- phases, elem (init (phaseName p)) optsPhasesToCount ]
        -- convert milliseconds -> seconds
        pure . Just $ PhasesSummary originalFilename (time / 1000) True
      _ ->
        error $ "can't parse: " ++ show fp
  let csvData = encodeDefaultOrderedByNameWith (defaultEncodeOptions { encUseCrLf = False }) $ catMaybes csvFields
  writeFile optsOutputFile csvData

main :: IO ()
main = program =<< execParser opts
