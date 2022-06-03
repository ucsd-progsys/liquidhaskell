{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Monad (guard, void)
import Data.String (fromString)
import Prelude hiding (writeFile)
import Data.Csv hiding (Options, Parser)
import Data.Aeson hiding (Options)
import GHC.Generics (Generic)
import Options.Applicative
import Data.Traversable (for)
import Data.Maybe (catMaybes)

import Text.Megaparsec (ParsecT, Parsec)
import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MP

import Data.ByteString.Lazy (ByteString)
import Data.ByteString.Lazy.Char8 (writeFile)
import Data.List (intersperse)
import Data.Void (Void)

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

-- | Parse the original filename from the .dump-timings filename
dumpFilenameParser :: MP.Parsec Void String FilePath
dumpFilenameParser = do
  _arch <- element "--"
  _ghcVersion <- element "--"
  _pkg <- element "--"
  pathPieces <- MP.manyTill (element ("--" <|> ".")) "dump-timings.json"
  MP.eof
  pure . mconcat $ intersperse "/" pathPieces
  where
    element = MP.manyTill MP.anySingle

program :: Options -> IO ()
program Options {..} = do
  csvFields <- for optsFilesToParse $ \fp -> do
    -- irrefutably get the filename and fail if we can't!
    let Just originalFilename = MP.parseMaybe dumpFilenameParser fp
    Just (phases :: [Phase]) <- decodeFileStrict' fp
    let (_modName, time) = foldr (\Phase {..} (_, acc) -> (phaseModule,
                                                          if init phaseName `elem` optsPhasesToCount then acc + phaseTime else acc)) ("", 0) phases
    -- convert milliseconds -> seconds
    pure . Just $ PhasesSummary originalFilename (time / 1000) True
  let csvData = encodeDefaultOrderedByNameWith (defaultEncodeOptions { encUseCrLf = False }) $ catMaybes csvFields
  writeFile optsOutputFile csvData

main :: IO ()
main = program =<< execParser opts
