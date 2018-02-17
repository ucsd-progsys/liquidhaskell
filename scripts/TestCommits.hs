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
-- project = "liquidhaskell --fast --test-arguments=\"-p Peano\""

branch :: String
branch = "develop"

tmpFile :: FilePath
tmpFile = "/tmp/commits"

summaryPath :: FilePath
summaryPath = "/Users/rjhala/research/stack/lh-test/tests/logs/cur/summary.csv"

--------------------------------------------------------------------------------
main :: IO ()
--------------------------------------------------------------------------------
main = do
  p <- strParam . head <$> getArgs
  case p of
    File f -> testCommits f
    Size n -> makeCommits n

makeCommits :: Int -> IO ()
makeCommits n = do
  system (genCommand n)
  putStrLn $ "Wrote commits into: " ++ tmpFile

testCommits :: FilePath -> IO ()
testCommits f = do
  is <- readCommits f
  putStrLn "Generating test summaries for:"
  mapM_ (putStrLn . ("  " ++)) is
  runCmd setupCmd
  mapM_ runCommit is
  runCmd setupCmd

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
_commits :: Param -> IO [CommitId]
--------------------------------------------------------------------------------
_commits (File f) = readCommits f
_commits (Size n) = system (genCommand n) >> readCommits tmpFile

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
  , printf "cp %s ~/tmp/summary-%s.csv" summaryPath i
  ]

