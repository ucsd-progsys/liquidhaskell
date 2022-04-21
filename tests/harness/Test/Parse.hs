-- * TODO: Switch to json parsing when liquid becomes more amenable to it.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Test.Parse where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Text.Megaparsec as P
import qualified Text.Megaparsec.Char as P
import qualified Text.Megaparsec.Char.Lexer as P hiding (space)
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.List as L
import Data.Maybe (fromMaybe)
import Data.Void (Void)
import Text.Megaparsec (ParseErrorBundle)
import Control.Monad (void, (<=<))
import Control.Applicative ((<|>))
import Test.Types

-- * The line of attack is to parse the stdout and stderr separately, and then
--   use the filespans in the error messages to associate them with the module
--   names.

-- | Find the first `moduleInfo`, skipping anything that doesn't look like one
skipStartupTrash :: Parser ()
skipStartupTrash = void $ P.many $ do
  P.notFollowedBy $ P.try moduleInfo
  skipRestOfLine

-- | GHC does a bunch of linking and stuff at the end. We don't care about this,
-- but we want to parse it specifically so that we know we are near eof.
skipEndingTrash :: Parser ()
skipEndingTrash = void $ P.many $ do
  (void $ P.chunk "initializing"
    <|> P.chunk "Chasing dependencies: "
    <|> P.chunk "Linking "
    <|> P.chunk "systool:")
  skipRestOfLine

skipRestOfLine :: Parser ()
skipRestOfLine = P.takeWhileP Nothing (/= '\n') *> void P.eol

-- | Parse a `ModuleName`, which is assumed to not contain spaces, stopping
-- before the first space afterwards.
moduleName :: Parser ModuleName
moduleName = do
  first <- P.upperChar
  rest <- P.takeWhileP Nothing (\x -> x /= ' ' && x /= '\n')
  pure $ first `T.cons` rest

-- | This is the stdout parser for things that look like:
--
-- [ 23 of 164] Compiling My.Module ...<stuff we don't care about>...
--
-- followed by warnings we don't care about and that aren't printed as JSON:
--
-- WARNING: ...<stuff we don't care about>...
compilerHeader :: Parser CompilerHeader
compilerHeader = do
  void $ P.single '['
  void $ P.many $ P.single ' '
  chIndex <- P.decimal
  void $ P.chunk " of "
  chTotal <- P.decimal
  void $ P.single ']'
  void $ P.chunk " Compiling "
  chModule <- moduleName
  skipRestOfLine
  void $ P.many spuriousWarning
  P.option () (void P.eol)
  pure CompilerHeader {..}

-- | Parse a trace that probably was left in by accident.
spuriousTrace :: Parser ()
spuriousTrace = do
  void $ P.chunk "Trace: "
  skipRestOfLine
  void P.eol

-- | Parse a warning, optionally followed by advice
spuriousWarning :: Parser ()
spuriousWarning = do
  void $ P.chunk "WARNING:"
  skipRestOfLine
  P.option () $ do
    P.try $ void $ (P.chunk "Disable") <|> P.chunk "Enable"
    skipRestOfLine
    void P.eol

-- | All of `-ddump-timings` output get streamed to stdout, even with
-- `-ddump-to-file` on, so we must filter this. Luckily, it all starts with
-- three asterisks.
ddumpTimingsOutput :: Parser ()
ddumpTimingsOutput = do
  void $ P.chunk "*** "
  skipRestOfLine

-- | Parse something that looks like:
--
-- "myDirectory\/Module\/Of\/Power.hs:23:32: "
--
-- Note the space at the end is consumed.
fileSpan :: Parser FileSpan
fileSpan = do
  maybeUnknownLocation <- P.option Nothing $ Just <$> (P.try (P.chunk "<no location info>") <* P.chunk ": ")
  case maybeUnknownLocation of
    Just loc -> pure $ UnknownLocation $ T.unpack loc
    Nothing -> do
      fsName <- T.unpack . T.stripStart <$> (P.takeWhileP Nothing (/= ':'))
      void $ P.single ':'
      fsLine <- P.decimal
      void $ P.single ':'
      fsColumn <- P.decimal
      void $ P.chunk ": "
      pure FileSpan {..}

-- | Parse any line.
line :: Parser Text
line = do
  P.takeWhileP Nothing (/= '\n') <* void P.eol

-- | If GHC panics, we need to know, since this kills the compilation for all
-- subsequent files in the `TestGroup` as well.
ghcPanic :: Parser GhcPanic
ghcPanic = do
  gpHeader <- P.chunk "ghc: panic! (the 'impossible' happened)" <* P.eol
  gpBody <- T.unlines <$> (P.many $ do
    P.notFollowedBy $ P.try $ P.chunk "Please report this"
    line)
  gpPleaseReport <- line
  P.space
  pure GhcPanic {..}

-- | This is the main stderr parser. It's rather complex, but basically it
-- watches for specific strings that GHC has been known to spew out, and skip
-- them, keeping the error messages intact.  This catches:
--
-- * panics
-- * normal errors and warnings (which it later returns)
-- * -fkeep-going messages, where GHC helpfully tells you it's going to skip
--   some files because a prerequisite for them didn't compile.
--
-- Note that all errors and warnings are assumed to contain location information
-- in the form:
--
--    |
-- 34 | let someSpot = here in theCode
--    |     ^^^^^^^^
--
-- Because we aren't parsing JSON yet, this is our "delimiter" for the end of a
-- message. The important parts are the spaces, pipes (|) and number. The rest is
-- skipped.
compilerMessage :: TestGroupName -> Parser (Either ErrorException CompilerMessage)
compilerMessage testGroupName = do
  P.option () (void $ P.many $ spuriousWarning <|> spuriousTrace)
  panic <- P.option Nothing $ Just <$> ghcPanic
  case panic of
    Just p -> pure $ Left $ GhcPanicException testGroupName p
    Nothing -> do
      cmSpan <- fileSpan
      cmMood <- (MError <$ P.chunk "error") <|> (MWarning <$ P.chunk "warning")
      void $ P.single ':'
      skipRestOfLine
      cmMessage <- P.option "" $ do 
        m <- message
        P.option () fKeepGoingMessages
        P.option () (void $ P.many $ spuriousWarning <|> spuriousTrace)
        pure m
      pure $ Right CompilerMessage {..}
  where
    -- TODO(matt) should this be printed?
    fKeepGoingMessages :: Parser ()
    fKeepGoingMessages = void $ do
      P.chunk "-fkeep-going in use," *> skipRestOfLine
      P.many $ do
        P.notFollowedBy P.eol
        skipRestOfLine

    -- lines that look like:
    --     |
    -- 123 | here is the error!
    --     | ^^^^
    --
    spanLines :: Parser [Text]
    spanLines = do
      l1 <- bumperLine
      lineNumber <- T.pack . show <$> (P.decimal :: Parser Int)
      spcs <- P.many $ P.chunk " "
      restOfLine <- line
      let middleLine = T.concat $ [ lineNumber ] <> spcs <> [ restOfLine ]
      l2 <- bumperLine
      pure $ [l1, middleLine, l2]

      where
        bumperLine :: Parser Text
        bumperLine = do
          spcs <- P.many $ P.chunk " "
          barChar <- P.chunk "|"
          restOfLine <- line
          pure $ T.concat $ spcs <> [ barChar, restOfLine ]

    message :: Parser Text
    message = do
      initialLines <- P.many $ do
        P.notFollowedBy $ P.try spanLines
        line
      hereLines <- spanLines
      pure $ T.unlines $ initialLines <> hereLines

-- | Parse a `ModuleInfo`, leaving the `miMessages` blank for now, but see
-- `Summary.hs` for how they end up in there.
moduleInfo :: Parser ModuleInfo
moduleInfo = do
  miHeader <- compilerHeader
  miMessages <- pure [] -- The messages are stored in stderr
  pure ModuleInfo {..}

-- | Emitted when no changes require the test group to be recompiled.
upToDate :: Parser ()
upToDate = P.chunk "Up to date" *> void P.eol

-- | Top level stdout parser
results :: TestGroupData -> Parser (Either ResultsException [ModuleInfo])
results TestGroupData {..} =
  (Left (UpToDateException tgdName) <$ upToDate)
  <|> (do
          skipStartupTrash
          xs <- P.many moduleInfo
          skipEndingTrash
          if null xs
            then pure $ Left $ EmptyResultsException tgdName
            else pure $ Right xs)

-- | Parse a segfault message
segFault :: TestGroupName -> Parser ErrorException
segFault n = SegFaultException n <$ do
  P.try $ do
    void $ P.chunk "cabal: Failed to build "
    skipRestOfLine
  P.chunk "segfaulted (i.e. SIGSEGV)."

-- | Parse a double free message
doubleFree :: TestGroupName -> Parser ErrorException
doubleFree n = DoubleFreeException n <$ P.chunk "double free or corruption (out)"

-- | Top level stderr parser. Uses the list of directories in a `TestGroupData`
-- to properly nail down the moduleName. See `safeModuleName` in `Types.hs` for
-- details.
errorMap :: TestGroupData -> Parser (Either ErrorException (Map (Maybe ModuleName) [CompilerMessage]))
errorMap tgd@TestGroupData {..} = do
  segFaultOrDoubleFree <- P.option Nothing (Just <$> (segFault tgdName <|> doubleFree tgdName))
  case segFaultOrDoubleFree of
    Just ex -> pure $ Left ex
    Nothing -> do
      P.option () (void $ P.many $ P.chunk "Unknown flag: -B" *> P.eol)
      messages <- compilerMessage tgdName `P.sepEndBy` P.space
      pure $ do
        msgs <- sequence messages
        let grouped = L.groupBy (\m n -> fsName (cmSpan m) == fsName (cmSpan n)) msgs
        pure $ M.unions $ M.unionsWith (<>) <$> toMaps <$> grouped
  where
    toMaps :: [CompilerMessage] -> [Map (Maybe ModuleName) [CompilerMessage]]
    toMaps [] = mempty
    toMaps msgs@(x:_) = M.fromList . (\msg -> [(safeModuleName tgd $ fsName $ cmSpan x, [msg])]) <$> msgs

-- | Remove all lines that are from -ddump-timings from the input Text.
stripDDumpTimingsOutput :: Text -> Text
stripDDumpTimingsOutput = T.unlines . filter (not . ("*** " `T.isPrefixOf`)) . T.lines

-- | Remove the header for "tests> " if it exists on a line.
stripStackHeader :: Text -> Text
stripStackHeader = T.unlines
                   . fmap (\x ->
                             fromMaybe x
                             $     T.stripPrefix "> "
                               <=< (pure . T.stripStart)
                               <=< T.stripPrefix "tests"
                             $ x)
                   . T.lines

-- | Filter out all the messages we don't care about from the stack output
stripStackExtraneousMessages :: Text -> Text
stripStackExtraneousMessages = T.stripStart
                               . T.unlines
                               . throwOutFooter
                               . filter (\x ->
                                           not $
                                              "configure (exe)" `T.isSuffixOf` x
                                           || "contigure (lib)" `T.isSuffixOf` x
                                           || "build (lib)" `T.isSuffixOf` x
                                           || "copy/register" `T.isSuffixOf` x
                                           || "build (exe)" `T.isSuffixOf` x
                                           || "Configuring " `T.isPrefixOf` x
                                           || "Building all executables for" `T.isPrefixOf` x
                                           || "Preprocessing executable " `T.isPrefixOf` x
                                           || "Building executable" `T.isPrefixOf` x
                                           || "Chasing dependencies:" `T.isPrefixOf` x
                                           || "initializing package database:" `T.isPrefixOf` x
                                           || "Installing executable " `T.isPrefixOf` x
                                           || "Linking " `T.isPrefixOf` x
                                           || "systool:" `T.isPrefixOf` x
                                           || "Completed " `T.isPrefixOf` x
                                           || "WARNING: " `T.isPrefixOf` x
                                           || "Disable expansion" `T.isPrefixOf` x
                                           || "Enable expansion" `T.isPrefixOf` x)
                               . T.lines
  where
    -- | throw out everything after a magic string indicating compilation is
    -- complete
    throwOutFooter = go []
    go acc [] = reverse acc
    go acc (x:xs)
      | "--  While building package" `T.isPrefixOf` x = reverse acc
      | otherwise = go (x : acc) xs

-- | Use this function to parse stdout.
parseResults :: TestGroupData -> Text -> Either (ParseErrorBundle Text Void) (Either ResultsException [ModuleInfo])
parseResults tgd = P.parse (results tgd <* P.space <* P.eof) "<cabal-install stdout>"

-- | Use this function to parse stderr.
parseErrors :: TestGroupData -> Text -> Either (ParseErrorBundle Text Void) (Either ErrorException (Map (Maybe ModuleName) [CompilerMessage]))
parseErrors tgd = P.parse (P.space *> errorMap tgd <* P.space <* P.eof) "<cabal-install stderr>"
