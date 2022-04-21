{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RecordWildCards #-}

module Test.Build where

import qualified Shelly as Sh
import Shelly (Sh)
import qualified Data.Map as M
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Test.Groups
import Test.Summary
import Data.Traversable (for)
import System.Exit (exitSuccess, exitFailure)
import qualified Data.ByteString.Lazy as BS
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.Encoding as TE
import qualified Text.Megaparsec as P
import Data.Map (Map)
import Data.Maybe (catMaybes)
import Data.List (partition, intersperse)
import Test.Types
import Test.Parse hiding (results)
import System.Process.Typed
import Control.Monad (void)
import Data.String.AnsiEscapeCodes.Strip.Text (stripAnsiEscapeCodes)
import System.Environment

-- | Whether or not we want to only build the dependencies of a library (to help
-- sanitize the compiler output)
type OnlyDeps = Bool

-- | Simple wrapper around `readProcess` and `proc` of `System.Process.Typed`.
-- Collects an exit code, stdout, and stderr.
command :: Text -> [Text] -> IO (ExitCode, Text, Text)
command cmd args = do
  (ec, out, err) <- readProcess (proc (T.unpack cmd) (T.unpack <$> args))
  pure (ec, toText out, toText err)
  where
    toText = TE.decodeUtf8 . BS.toStrict

-- | Build using cabal, selecting the project file from the
-- `LIQUID_CABAL_PROJECT_FILE` environment variable if possible, otherwise using
-- the default.
cabalBuild :: OnlyDeps -> TestGroupName -> IO (ExitCode, Text, Text)
cabalBuild onlyDeps name = do
  projectFile <- lookupEnv "LIQUID_CABAL_PROJECT_FILE"
  command "cabal" $
    [ "build" ]
    <> (if onlyDeps then [ "--only-dependencies" ] else [])
    <> (case projectFile of Nothing -> []; Just projectFile' -> [ "--project-file", T.pack projectFile' ])
    <> [ name ]

-- | Build using stack. This *emulates* the output of the cabalBuild by splitting
-- the interleaved stdout/stderr that stack normally outputs into two Texts.
stackBuild :: OnlyDeps -> TestGroupName -> IO (ExitCode, Text, Text)
stackBuild onlyDeps name = do
  (ec, _out, err) <- command "stack" $
     [ "build"
     , "--flag", "tests:stack"
       -- Enables that particular executable in the cabal file
     , "--flag", ("tests:" <> name)
     , "--no-interleaved-output" ]
     <> (if onlyDeps then [ "--only-dependencies" ] else [])
     <> [ "--" ]
     <> [ "tests:" <> name ]
  let (buildMsgs, errMsgs) = partition ("[" `T.isPrefixOf`) (T.lines err)
  T.putStrLn _out
  pure (ec, T.unlines $ intersperse "" buildMsgs, T.unlines errMsgs)

-- | Given a "builder" command and some `TestGroupData`, create an IO action
-- that parses the results of running the build command. Outputs can be fed into
-- functions in `Summary.hs`.
buildAndParseResults
  :: (Text -> Text)
  -> (Text -> Text)
  -> (OnlyDeps -> TestGroupName -> IO (ExitCode, Text, Text))
  -> TestGroupData
  -> IO (Either ErrorException (Map (Maybe ModuleName) [CompilerMessage]), Either ResultsException [ModuleInfo])
buildAndParseResults outputStripper errorStripper builder tgd@TestGroupData {..} = do
  T.putStrLn $ "Ensuring dependencies for " <> tgdName <> " are up to date..."
  void $ builder True tgdName
  T.putStrLn $ "Building " <> tgdName <> " for real now!"
  (_, out', err') <- builder False tgdName
  let out = outputStripper out'
      err = errorStripper err'
  T.putStrLn out
  T.putStrLn $ "*** STDERR " <> tgdName <> " ***\n" <> err <> "\n*** END STDERR " <> tgdName <> " ***\n"
  errMap <-
    either
      ((>> (pure $ Left $ FishyErrorParseException tgdName)) . printError)
      pure
      $ parseErrors tgd err
  results <-
    either
      ((>> (pure $ Left $ FishyResultsParseException tgdName)) . printError)
      pure
      $ parseResults tgd out
  pure (errMap, results)
  where
    printError = T.putStrLn . T.pack . P.errorBundlePretty

-- | Ensure prog is on the PATH
ensurePathContains :: Text -> Sh ()
ensurePathContains prog =
  Sh.unlessM (Sh.test_px $ T.unpack prog) $ do
    Sh.errorExit $ "Cannot find " <> prog <> " on the path."

-- | Make sure cabal is available
cabalTestEnv :: Sh ()
cabalTestEnv = ensurePathContains "cabal"

-- | Strip colors and so on from stdout
cabalOutputStripper :: Text -> Text
cabalOutputStripper = stripAnsiEscapeCodes

-- | Strip colors and -ddump-timings noise from stderr
cabalErrorStripper :: Text -> Text
cabalErrorStripper = stripDDumpTimingsOutput . stripAnsiEscapeCodes

-- | Make sure stack is available
stackTestEnv :: Sh ()
stackTestEnv = ensurePathContains "stack"

-- | Strip colors and the stack header from "stdout" (see stackBuild; not
-- actually stdout)
stackOutputStripper :: Text -> Text
stackOutputStripper = cabalOutputStripper . stripStackHeader

-- | Strip colors and extra messages from "stderr" (see stackBuild; not actually
-- stderr)
stackErrorStripper :: Text -> Text
stackErrorStripper = cabalErrorStripper . stripStackExtraneousMessages . stripStackHeader

-- | For building `main`; provided so that we don't repeat outselves in
-- "Driver_cabal.hs" and "Driver_stack.hs"
program :: Sh () -> (Text -> Text) -> (Text -> Text) -> (OnlyDeps -> TestGroupName -> IO (ExitCode, Text, Text)) -> Options -> IO ()
program _ _ _ _ (Options _ True) = do
  void $ for allTestGroupNames T.putStrLn
  exitSuccess
program testEnv outputStripper errorStripper builder os@(Options _ False) = do
  Sh.shelly testEnv
  allTestGroupsMap <- allTestGroups
  let selectedGroups = for (testGroups os) $ \name -> M.lookup name allTestGroupsMap
  case selectedGroups of
    Nothing -> do
      T.putStrLn "You selected a bad test group name.  Run with --help to see available options."
      exitFailure
    Just testGroupsSelected -> do
      let selectedTestGroups = if null testGroupsSelected then snd <$> M.toList allTestGroupsMap else testGroupsSelected
      flagsAndActions <- for selectedTestGroups $ \tgd -> do
        (err, res) <- buildAndParseResults outputStripper errorStripper builder tgd
        let (flag, action, numRan) =
              case (err, res) of
                (Left errException, Left resException) ->
                  (True, printError errException >> printError resException, Nothing)
                (Left errException, _) -> (True, printError errException, Nothing)
                (_, Left resException) -> (True, printError resException, Nothing)
                (Right err', Right res') ->
                  let
                    summary = summarizeResults err' tgd res'
                  in
                    ( False
                    , PP.putDoc $ PP.pretty summary PP.<$> PP.empty
                    , Just $ numberRan $ misSummary summary)
        action
        pure (flag, action, numRan)
      T.putStrLn "\n*** SUMMARY ***"
      -- Redo all the actions in a summary
      void $ traverse (\(_, action, _) -> action) flagsAndActions
      T.putStrLn "*** END SUMMARY ***\n"
      T.putStrLn $ "Total tests ran: " <> (T.pack $ show $ sum $ catMaybes $ fmap (\(_, _, numRan) -> numRan) flagsAndActions)
      if any (\(flag, _ , _) -> flag) flagsAndActions
        then do
          T.putStrLn "Something went wrong, please check the above output."
          exitFailure
        else do
          T.putStrLn "All tests passed!"
          exitSuccess
  where
    printError :: PP.Pretty a => a -> IO ()
    printError x = PP.putDoc $ PP.pretty x PP.<$> PP.empty

