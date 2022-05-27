{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Test.Types where

import Control.Applicative
import Data.Text (Text)
import qualified Data.Text as T
import Data.List (find)
import Data.Map (Map)
import Data.Void (Void)
import Text.Megaparsec (Parsec)
import Text.PrettyPrint.ANSI.Leijen (Pretty(..))
import qualified Text.PrettyPrint.ANSI.Leijen as PP

nesting :: Int
nesting = 2

type ErrorMsg      = Text
type TestGroupName = Text
type ModuleName    = Text
type ModulePath    = Text

type ConstraintsChecked = Int

type Parser = Parsec Void Text

data Options = Options
  { testGroups :: [TestGroupName]
  , showAll :: Bool
  }
  deriving stock (Eq, Ord, Show)

data TestGroupData = TestGroupData
  { tgdName :: TestGroupName
  , tgdDirectories :: [Text]
  , tgdFlavor :: TestFlavor }
  deriving stock (Eq, Ord, Show)

-- | The "flavor" of the test group.
--
-- * `TFSafe` is for groups of modules we want Liquid to declare as safe
-- * `TFUnsafe` is for groups of tests whose compilation we want to fail, but
--   whose error messages we don't really care about
-- * `TFError` is for groups of tests whose compilation we want to fail, along
--   with a map of module names to snippets of error messages we want the
--   failures to contain.
-- XXX(matt): can you remove `TFBench`?
-- * TFBench is a hold over and may be removed, but currently is the same as TFSafe
data TestFlavor =
    TFSafe
  | TFUnsafe
  | TFError (Map (Maybe ModuleName) ErrorMsg)
  | TFBench
  deriving stock (Eq, Ord, Show)

-- | Representation of the location information given to use by the compiler.
-- IMPORTANT: it is assumed we can always take the `fsName` of a `FileSpan`.
data FileSpan =
    FileSpan
    { fsName :: FilePath
    , fsLine :: Int
    , fsColumn :: Int
    }
  | UnknownLocation
    { fsName :: FilePath } -- will always be "<no location info>"
  deriving stock (Eq, Ord, Show)

instance Pretty FileSpan where
  pretty UnknownLocation {..} = PP.magenta (PP.text fsName) <> PP.char ':'
  pretty FileSpan {..} =
    PP.magenta (PP.text fsName)
    <> PP.char ':'
    <> PP.text (show fsLine)
    <> PP.char ':'
    <> PP.text (show fsColumn)
    <> PP.char ':'

-- | Obtain the first reasonable `ModuleName` possible given the
-- `tgdDirectories` by stripping them off the front of the `FilePath`, and
-- converting path seps to periods. Fail with `empty` if none of them work.
safeModuleName :: Alternative f => TestGroupData -> FilePath -> f ModuleName
safeModuleName TestGroupData {..} fp' =
  case (find (`T.isPrefixOf` fp) tgdDirectories, ".hs" `T.isSuffixOf` fp) of
    (Just tgdDirectory, True) -> pure $ T.map pathSepReplacer $ T.dropEnd 3 $ T.drop (T.length tgdDirectory + 1) fp
    _ -> empty
  where
    fp :: Text
    fp = T.pack fp'

    pathSepReplacer :: Char -> Char
    pathSepReplacer = \case
      '/' -> '.'
      '\\' -> '.'
      c -> c

-- | The "mood" of a warning or error message. Errors are assumed to accompany
-- abortion of the compilation for the module in question, and so are used to
-- judge the "safety" of it, according to Liquid.
data Mood =
    MWarning
  | MError
  deriving stock (Eq, Ord, Show)

instance Pretty Mood where
  pretty MWarning = PP.yellow (PP.text "warning")
  pretty MError = PP.red (PP.text "error")

-- | A complete information package containing everything we care about
-- regarding compilation of a module. Note that this will start off with an
-- empty `miMessages` in the parser, and will only be reunited with the messages
-- in `Summary.hs`
data ModuleInfo = ModuleInfo
  { miHeader :: CompilerHeader
  , miMessages :: [CompilerMessage]
  }
  deriving stock (Eq, Ord, Show)

instance Pretty ModuleInfo where
  pretty ModuleInfo {..} =
    pretty miHeader
    PP.<$> PP.indent nesting (PP.vsep $ pretty <$> miMessages)

-- | Which module are we compiling (and how many are there left?)
data CompilerHeader = CompilerHeader
  { chIndex :: Int
  , chTotal :: Int
  , chModule :: ModuleName
  }
  deriving stock (Eq, Ord, Show)

instance Pretty CompilerHeader where
  pretty CompilerHeader {..} =
    pretty chIndex
      <> PP.text " / "
      <> pretty chTotal
      <> PP.text ": "
      <> PP.text (T.unpack chModule)

-- | An error or warning message from GHC
data CompilerMessage = CompilerMessage
  { cmSpan :: FileSpan
  , cmMood :: Mood
  , cmMessage :: Text
  }
  deriving stock (Eq, Ord, Show)

instance Pretty CompilerMessage where
  pretty CompilerMessage {..} =
    (pretty cmSpan <> pretty cmMood)
    PP.<$> (PP.vsep $ PP.text . T.unpack <$> T.lines cmMessage)

-- | Strip out the colors and fancy bolding/underlining from a `CompilerMessage`
-- and return it in a reasonable (though not exactly identical) Text form,
-- similar to how it was displayed originally. Used to grep around for the
-- `ErrorMsg` fragments in `TFError`-flavored `TestGroup`s.
reshow :: CompilerMessage -> Text
reshow = T.pack . show . PP.plain . pretty

-- | An `a`-flavored summary of all the compilations in this `TestGroupData`. We
-- sometimes call `()`-flavored summaries "vanilla".
data ModuleInfoSummary a =
  ModuleInfoSummary
  { misRan :: ![ModuleInfo]
  , misSafe :: ![ModuleInfo]
  , misUnsafe :: ![ModuleInfo]
  , misData :: TestGroupData
  , misSummary :: a
  }
  deriving stock (Eq, Ord, Show)

instance Pretty (ModuleInfoSummary FlavorSummary) where
  pretty ModuleInfoSummary {..} =
    PP.magenta (PP.text (T.unpack $ tgdName misData))
    <> PP.char ':'
    PP.<$> pretty misSummary

-- | The number of modules ran attempted to be compiled in total
type NumberRan = Int

data FlavorSummary =
    FSAllGood NumberRan
  | FSUnexpected
      NumberRan -- ^ number of total modules checked
      [ModuleInfo] -- ^ modules which had unexpected output
      (Maybe [(ModuleInfo, ErrorMsg)]) -- ^ modules which had the wrong error messages (if relevant)
  deriving stock (Eq, Ord, Show)

numberRan :: FlavorSummary -> NumberRan
numberRan (FSAllGood ran) = ran
numberRan (FSUnexpected ran _ _) = ran

instance Pretty FlavorSummary where
  pretty (FSAllGood ran) =
    PP.indent nesting $
      PP.green (PP.text "All good")
      <> PP.text (" (" <> show ran <> " modules checked)")
  pretty (FSUnexpected ran xs mismatches) =
    PP.indent nesting $
    PP.red (PP.text "Unexpected") PP.<> PP.text (" (" <> show (length xs) <> "/" <> show ran <> " modules failed)")
    PP.<$> (PP.indent nesting $
             list' xs
             PP.<$> (maybe PP.empty (PP.vsep . fmap (\(mi, err) ->
                                                        (PP.text "The error messages of:")
                                                        PP.<$> pretty mi
                                                        PP.<$> (PP.text "didn't match expected error message of:")
                                                        PP.<$> (PP.red $ PP.text $ T.unpack err))) mismatches))
    where list' = PP.vsep . fmap pretty

-- | An Exception for parsing stdout when things look wrong. NOT necessarily a
-- parsing error, just a result that indicates that parsing didn't turn up what
-- we expected. "Fishy" parses are ones which we don't recognize for whatever
-- reason. `UpToDateException` is here because in such a case the tests were not
-- actually run. Sometimes when you change a cabal file in a certain way, it
-- will not say "Up to date", but will also not compile anything. That is the
-- situation `EmptyResultsException` indicates.
data ResultsException =
    UpToDateException TestGroupName
  | FishyResultsParseException TestGroupName
  | EmptyResultsException TestGroupName
  deriving stock (Eq, Ord, Show)

instance Pretty ResultsException where
  pretty (UpToDateException test) =
    PP.magenta (PP.text (T.unpack test)) <> PP.text " has already been compiled, so " <> PP.red (PP.text "the entire test group has not run") <> PP.text "."
  pretty (FishyResultsParseException test) =
    PP.magenta (PP.text (T.unpack test)) <> PP.text " had " <> PP.red (PP.text "fishy output") <> PP.text " from parser when attempting to scan stdout."
  pretty (EmptyResultsException test) =
    PP.magenta (PP.text (T.unpack test)) <> PP.text " " <> PP.red (PP.text "didn't compile any modules") <> PP.text "."

-- | An Exception for parsing stderr when things look wrong. NOT necessarily a
-- parsing error, just a result that indicates that parsing didn't turn up what
-- we expected. `GhcPanicException` are if GHC panics; remember that this aborts
-- the compilation of other modules in the TestGroup, so should be be viewed as
-- a fairly major bug. "Fishy" parses are anything that we don't recognize.
data ErrorException =
    GhcPanicException TestGroupName GhcPanic
  | SegFaultException TestGroupName
  | DoubleFreeException TestGroupName
  | FishyErrorParseException TestGroupName
  deriving stock (Eq, Ord, Show)

instance Pretty ErrorException where
  pretty (GhcPanicException test panic) =
    PP.magenta (PP.text (T.unpack test)) <> PP.text " caused ghc to " <> PP.red (PP.text "panic") <> PP.text " with message:"
    PP.<$> (PP.indent nesting $ pretty panic)
  pretty (SegFaultException test) =
    PP.magenta (PP.text (T.unpack test)) <> PP.text " caused ghc to " <> PP.red (PP.text "segfault") <> PP.text "."
  pretty (DoubleFreeException test) =
    PP.magenta (PP.text (T.unpack test)) <> PP.text " caused ghc to " <> PP.red (PP.text "call free twice on memory") <> PP.text "."
  pretty (FishyErrorParseException test) =
    PP.magenta (PP.text (T.unpack test)) <> PP.text " had " <> PP.red (PP.text "fishy output") <> PP.text " from parser when attempting to scan stderr."

-- | A fairly unstructured panic, suitable only for regurgitating the message.
-- Do not try to recover; fix the code.
data GhcPanic = GhcPanic
  { gpHeader :: Text
  , gpBody   :: Text
  , gpPleaseReport :: Text
  }
  deriving stock (Eq, Ord, Show)

instance Pretty GhcPanic where
  pretty GhcPanic {..} =
    PP.text (T.unpack gpHeader)
    PP.<$> PP.text (T.unpack gpBody)
    PP.<$> PP.text (T.unpack gpPleaseReport)
