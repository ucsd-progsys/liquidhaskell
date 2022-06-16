{-# LANGUAGE OverloadedStrings #-}

module Test.Build where

import qualified Shelly as Sh
import Shelly (Sh)
import Test.Groups
import Test.Options (Options(..))
import System.Exit (exitSuccess, exitFailure, exitWith)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.Process.Typed
import System.Environment
import Data.Foldable (for_)

-- | Wrapper around runProcess that just returns the exit code.
runCommand :: Text -> [Text] -> IO ExitCode
runCommand cmd args = runProcess (proc (T.unpack cmd) (T.unpack <$> args))

-- | Build using cabal, selecting the project file from the
-- `LIQUID_CABAL_PROJECT_FILE` environment variable if possible, otherwise using
-- the default.
cabalRun :: [Text] -- ^ Test groups to build
         -> IO ExitCode
cabalRun names = do
  projectFile <- lookupEnv "LIQUID_CABAL_PROJECT_FILE"
  runCommand "cabal" $
    [ "build" ]
    <> (case projectFile of Nothing -> []; Just projectFile' -> [ "--project-file", T.pack projectFile' ])
    <> ["-j", "--keep-going"]
    <> names

-- | Runs stack on the given test groups
stackRun :: [Text] -> IO ExitCode
stackRun names =
  runCommand "stack" $
    [ "build"
    , "--flag", "tests:stack" ]
    -- Enables that particular executable in the cabal file
    <> testFlags
    <> [ "--" ]
    <> testNames
  where
    testNames = fmap ("tests:" <>) names
    testFlags = concatMap (("--flag" :) . pure) testNames

build :: ([Text] -> IO ExitCode) -> [Text] -> IO ExitCode
build builder tgns = do
  T.putStrLn "Running integration tests!"
  builder tgns

-- | Ensure prog is on the PATH
ensurePathContains :: Text -> Sh ()
ensurePathContains prog =
  Sh.unlessM (Sh.test_px $ T.unpack prog) $ do
    Sh.errorExit $ "Cannot find " <> prog <> " on the path."

-- | Make sure cabal is available
cabalTestEnv :: Sh ()
cabalTestEnv = ensurePathContains "cabal"

-- | Make sure stack is available
stackTestEnv :: Sh ()
stackTestEnv = ensurePathContains "stack"

-- | Main program; reused between cabal and stack drivers
program :: Sh () -> ([Text] -> IO ExitCode) -> Options ->IO ()
program _ _ (Options _ True) = do
  for_ allTestGroupNames T.putStrLn
  exitSuccess
program testEnv runner (Options testGroups' False) = do
  Sh.shelly testEnv
  let goodGroups = all (`elem` allTestGroupNames) testGroups'
  if not goodGroups
    then do
      T.putStrLn "You selected a bad test group name.  Run with --help to see available options."
      exitFailure
    else do
      let selectedTestGroups = if null testGroups' then allTestGroupNames else testGroups'
      build runner selectedTestGroups >>= exitWith

