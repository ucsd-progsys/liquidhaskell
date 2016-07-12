#!/usr/bin/env runhaskell

{- GeneralizedNewtypeDeriving -}

import System.Environment   (getArgs)
import System.Process       (system)
import Text.Printf          (printf)
import Data.List            (isSuffixOf, stripPrefix)
import Data.Maybe           (fromMaybe)

{- | Run this script as:

     $ ./TestCommit.hs commits.txt

     where commits.txt is a file with a single git commit on each line, OR

     $ ./TestCommit.hs NUMBER

     which will get the last N(UMBER) of commits from the `branch`

 -}

--------------------------------------------------------------------------------
-- | Configuration parameters
--------------------------------------------------------------------------------

project :: String
project = "liquidhaskell"

branch :: String
branch = "develop"

tmpFile :: FilePath
tmpFile = "/tmp/commits"

--------------------------------------------------------------------------------
main :: IO ()
--------------------------------------------------------------------------------
main = do
  is <- commits =<< param
  putStrLn "Generating test summaries for:"
  mapM_ (putStrLn . ("  " ++)) is
  runCmd setupCmd
  mapM_ runCommit is

param :: IO Param
param = strParam . head <$> getArgs

strParam :: String -> Param
strParam s
  | ".txt" `isSuffixOf` s = File s
  | otherwise             = Size (read s)

--------------------------------------------------------------------------------
-- | Types
--------------------------------------------------------------------------------
data Param = File FilePath
           | Size Int

type CommitId = String
type Command  = [String]


--------------------------------------------------------------------------------
commits :: Param -> IO [CommitId]
--------------------------------------------------------------------------------
commits (File f) = readCommits f
commits (Size n) = system (genCommand n) >> readCommits tmpFile

genCommand :: Int -> String
genCommand n = printf "git log -n %d --walk-reflogs %s | grep \"commit \" > %s"
                 n branch tmpFile

readCommits :: FilePath -> IO [CommitId]
readCommits f = map strCommit . lines <$> readFile f

strCommit :: String -> CommitId
strCommit s = fromMaybe s (stripPrefix "commit " s)


--------------------------------------------------------------------------------
runCommit :: CommitId -> IO ()
--------------------------------------------------------------------------------
runCommit i = do
  putStrLn ("Running commit: " ++ i)
  runCmd (commitCmd i)

runCmd :: Command -> IO ()
runCmd = mapM_ system

setupCmd :: Command
setupCmd = [ printf "git checkout %s" branch ]

commitCmd :: CommitId -> Command
commitCmd i =
  [ printf "git checkout %s"       i
  ,        "git submodule update"
  , printf "stack test %s"         project
  , printf "cp tests/logs/cur/summary.csv test/logs/summary-%s.csv" i
  ]
