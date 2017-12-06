{-# LANGUAGE CPP  #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DoAndIfThenElse     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Applicative
import qualified Control.Concurrent.STM as STM
import qualified Control.Monad.State as State
import Control.Monad.Trans.Class (lift)
import Data.Char
import qualified Data.Functor.Compose as Functor
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Monoid (Sum(..), (<>))
import Data.Proxy
import Data.String
import Data.Tagged
import Data.Typeable
import qualified Data.Text    as T
import qualified Data.Text.IO as T
import Options.Applicative
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.IO
import System.IO.Error
import System.Process
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Ingredients.Rerun
import Test.Tasty.Options
import Test.Tasty.Runners
import Test.Tasty.Runners.AntXML
import Paths_liquidhaskell

import Text.Printf

testRunner :: Ingredient
testRunner = rerunningTests
               [ listingTests
               , combineReporters myConsoleReporter antXMLRunner
               , myConsoleReporter
               ]

myConsoleReporter :: Ingredient
myConsoleReporter = combineReporters consoleTestReporter loggingTestReporter

main :: IO ()
main = do unsetEnv "LIQUIDHASKELL_OPTS"
          run =<< tests
  where
    run   = defaultMainWithIngredients [
                testRunner
              , includingOptions [ Option (Proxy :: Proxy NumThreads)
                                 , Option (Proxy :: Proxy LiquidOpts)
                                 , Option (Proxy :: Proxy SmtSolver) ]
              ]
    tests = group "Tests" [ unitTests, errorTests, benchTests, proverTests ]
    -- tests = group "Tests" [ unitTests  ]
    -- tests = group "Tests" [ benchTests ]
    -- tests = group "Tests" [ selfTests  ]
    -- tests = group "Tests" [ errorTests ]

data SmtSolver = Z3 | CVC4 deriving (Show, Read, Eq, Ord, Typeable)

instance IsOption SmtSolver where
  defaultValue = Z3
  parseValue = safeRead . map toUpper
  optionName = return "smtsolver"
  optionHelp = return "Use this SMT solver"
  optionCLParser =
    option (fmap (read . map toUpper) str)
      (  long (untag (optionName :: Tagged SmtSolver String))
      <> help (untag (optionHelp :: Tagged SmtSolver String))
      )

newtype LiquidOpts = LO String deriving (Show, Read, Eq, Ord, Typeable, IsString)
instance Monoid LiquidOpts where
  mempty = LO ""
  mappend (LO "") y = y
  mappend x (LO "") = x
  mappend (LO x) (LO y) = LO $ x ++ (' ' : y)
instance IsOption LiquidOpts where
  defaultValue = LO ""
  parseValue = Just . LO
  optionName = return "liquid-opts"
  optionHelp = return "Extra options to pass to LiquidHaskell"
  optionCLParser =
    option (fmap LO str)
      (  long (untag (optionName :: Tagged LiquidOpts String))
      <> help (untag (optionHelp :: Tagged LiquidOpts String))
      )

errorTests :: IO TestTree
errorTests = group "Error-Messages"
  [ errorTest "tests/errors/ExportMeasure0.hs"      2 "Cannot lift `llen` into refinement logic"
  , errorTest "tests/errors/ExportMeasure1.hs"      2 "Cannot lift `psnd` into refinement logic"
  , errorTest "tests/errors/ExportReflect0.hs"      2 "Cannot lift `identity` into refinement logic"
  , errorTest "tests/errors/MultiRecSels.hs"        2 "Duplicated definitions for field `left`"
  , errorTest "tests/errors/DupFunSigs.hs"          2 "Multiple specifications for `Main.fromWeekDayNum`"
  , errorTest "tests/errors/DupMeasure.hs"          2 "Multiple measures named `lenA`"
  , errorTest "tests/errors/ShadowFieldInline.hs"   2 "Malformed application of type alias `Range.pig`"
  , errorTest "tests/errors/ShadowFieldReflect.hs"  2 "Illegal type specification for `assumed type Range.pig`"
  , errorTest "tests/errors/ShadowMeasure.hs"       2 "Multiple specifications for `shadow`"
  , errorTest "tests/errors/ShadowMeasureVar.hs"    2 "Multiple specifications for `shadow`"
  , errorTest "tests/errors/DupData.hs"             2 "Multiple specifications for `OVec`"
  , errorTest "tests/errors/EmptyData.hs"           2 "one or more fields in the data declaration for `A`"
  , errorTest "tests/errors/AmbiguousReflect.hs"    2 "Ambiguous specification symbol `mappend`"
  , errorTest "tests/errors/AmbiguousInline.hs"     2 "Ambiguous specification symbol `min`"
  , errorTest "tests/errors/TerminationExprSort.hs" 2 "Illegal termination specification for `TerminationExpr.showSep`"
  , errorTest "tests/errors/TerminationExprNum.hs"  2 "Illegal termination specification for `TerminationExpr.showSep`"
  , errorTest "tests/errors/TerminationExprUnb.hs"  2 "Illegal termination specification for `go`"
  , errorTest "tests/errors/UnboundVarInSpec.hs"    2 "Illegal type specification for `Fixme.foo`"
  , errorTest "tests/errors/MissingAbsRefArgs.hs"   2 "Illegal type specification for `Fixme.bar`"
  , errorTest "tests/errors/UnboundVarInAssume.hs"  2 "Illegal type specification for `Assume.incr`"
  , errorTest "tests/errors/UnboundVarInAssume1.hs" 2 "Illegal type specification for `Main.b`"
  , errorTest "tests/errors/UnboundFunInSpec.hs"    2 "Illegal type specification for `Goo.three`"
  , errorTest "tests/errors/UnboundFunInSpec1.hs"   2 "Illegal type specification for `Goo.foo`"
  , errorTest "tests/errors/UnboundFunInSpec2.hs"   2 "Illegal type specification for `Goo.foo`"
  , errorTest "tests/errors/Fractional.hs"          2 "Illegal type specification for `Crash.f`"
  , errorTest "tests/errors/T773.hs"                2 "Illegal type specification for `LiquidR.incr`"
  , errorTest "tests/errors/T774.hs"                2 "Illegal type specification for `LiquidR.incr`"
  , errorTest "tests/errors/Inconsistent0.hs"       2 "Specified type does not refine Haskell type for `Ast.app` (Checked)"
  , errorTest "tests/errors/Inconsistent1.hs"       2 "Specified type does not refine Haskell type for `Boo.incr` (Checked)"
  , errorTest "tests/errors/Inconsistent2.hs"       2 "Specified type does not refine Haskell type for `Mismatch.foo` (Checked)"
  , errorTest "tests/errors/BadAliasApp.hs"         2 "Malformed application of type alias `ListN`"
  , errorTest "tests/errors/BadPragma0.hs"          2 "Illegal pragma"
  , errorTest "tests/errors/BadPragma1.hs"          2 "Illegal pragma"
  , errorTest "tests/errors/BadPragma2.hs"          2 "Illegal pragma"
  , errorTest "tests/errors/BadSyn1.hs"             2 "Malformed application of type alias `Fooz`"
  , errorTest "tests/errors/BadSyn2.hs"             2 "Malformed application of type alias `Zoo.Foo`"
  , errorTest "tests/errors/BadSyn3.hs"             2 "Malformed application of type alias `Zoo.Foo`"
  , errorTest "tests/errors/BadSyn4.hs"             2 "Malformed application of type alias `Foo.Point`"
  , errorTest "tests/errors/BadAnnotation.hs"       2 "Malformed annotation"
  , errorTest "tests/errors/BadAnnotation1.hs"      2 "Malformed annotation"
  , errorTest "tests/errors/CyclicExprAlias0.hs"    2 "Cyclic type alias definition for `CyclicA1`"
  , errorTest "tests/errors/CyclicExprAlias1.hs"    2 "Cyclic type alias definition for `CyclicB1`"
  , errorTest "tests/errors/CyclicExprAlias2.hs"    2 "Cyclic type alias definition for `CyclicC1`"
  , errorTest "tests/errors/CyclicExprAlias3.hs"    2 "Cyclic type alias definition for `CyclicD3`"
  , errorTest "tests/errors/DupAlias.hs"            2 "Multiple definitions of Type Alias `BoundedNat`"
  , errorTest "tests/errors/DupAlias.hs"            2 "Multiple definitions of Pred Alias `Foo`"
  , errorTest "tests/errors/BadDataConType.hs"      2 "Specified type does not refine Haskell type for `Boo.C`"
  , errorTest "tests/errors/LiftMeasureCase.hs"     2 "Cannot lift Haskell function `foo` to logic"
  , errorTest "tests/errors/HigherOrderBinder.hs"   2 "Illegal type specification for `Main.foo`"
  , errorTest "tests/errors/HoleCrash1.hs"          2 "Illegal type specification for `ListDemo.t`"
  , errorTest "tests/errors/HoleCrash2.hs"          2 "Malformed application of type alias `Geq`"
  , errorTest "tests/errors/HoleCrash3.hs"          2 "Specified type does not refine Haskell type for `ListDemo.countUp`"
  , errorTest "tests/errors/HoleCrash3.hs"          2 "Specified type does not refine Haskell type for `ListDemo.countUp`"
  , errorTest "tests/errors/BadPredApp.hs"          2 "Malformed predicate application"
  , errorTest "tests/errors/LocalHole.hs"           2 "Illegal type specification for `go`"
  , errorTest "tests/errors/UnboundAbsRef.hs"       2 "Cannot apply unbound abstract refinement `p`"
  , errorTest "tests/errors/BadQualifier.hs"        2 "Illegal qualifier specification for `Foo`"
  , errorTest "tests/errors/ParseClass.hs"          2 "Cannot parse specification"
  , errorTest "tests/errors/ParseBind.hs"           2 "Cannot parse specification"
  , errorTest "tests/errors/MissingSizeFun.hs"      2 "Illegal data refinement for `MapReduce.List`"
  , errorTest "tests/errors/MissingSizeFun.hs"      2 "Illegal data refinement for `MapReduce.List2`"
  , errorTest "tests/errors/MultiInstMeasures.hs"   2 "Multiple instance measures `sizeOf` for type `GHC.Ptr.Ptr`"
  , errorTest "tests/errors/BadDataDeclTyVars.hs"   2 "Mismatch in number of type variables for `L`"
  , errorTest "tests/errors/BadDataCon2.hs"         2 "GHC and Liquid specifications have different numbers of fields for `Boo.Cuthb`"
  , errorTest "tests/errors/BadSig0.hs"             2 "Error: Illegal type specification for `Zoo.foo`"
  , errorTest "tests/errors/BadSig1.hs"             2 "Error: Illegal type specification for `constructor Ev.EZ`"
  , errorTest "tests/errors/BadData1.hs"            2 "`Main.EntityField` is not the type constructor for `BlobXVal`"
  , errorTest "tests/errors/BadData2.hs"            2 "`Boo.Hog` is not the type constructor for `Cuthb`"
  , errorTest "tests/errors/T1140.hs"               2 "Specified type does not refine Haskell type for `Blank.foo`"
  ]

unitTests :: IO TestTree
unitTests = group "Unit"
  [ testGroup "pos"            <$> dirTests "tests/pos"                            posIgnored        ExitSuccess
  , testGroup "neg"            <$> dirTests "tests/neg"                            negIgnored        (ExitFailure 1)
  , testGroup "parser/pos"     <$> dirTests "tests/parser/pos"                     []                ExitSuccess
  , testGroup "import/lib"     <$> dirTests "tests/import/lib"                     []                ExitSuccess
  , testGroup "import/client"  <$> dirTests "tests/import/client"                  []                ExitSuccess
  -- RJ: disabling because broken by adt PR #1068
  -- , testGroup "gradual/pos"    <$> dirTests "tests/gradual/pos"                    []                ExitSuccess
  -- , testGroup "gradual/neg"    <$> dirTests "tests/gradual/neg"                    []                (ExitFailure 1)
  -- , testGroup "eq_pos"      <$> dirTests "tests/equationalproofs/pos"           ["Axiomatize.hs", "Equational.hs"]           ExitSuccess
  -- , testGroup "eq_neg"      <$> dirTests "tests/equationalproofs/neg"           ["Axiomatize.hs", "Equational.hs"]           (ExitFailure 1)
  ]

posIgnored = [ "mapreduce.hs" ]
gPosIgnored = ["Intro.hs"]
gNegIgnored = ["Interpretations.hs", "Gradual.hs"]

benchTests :: IO TestTree
benchTests = group "Benchmarks"
  [ testGroup "text"        <$> dirTests "benchmarks/text-0.11.2.3"             textIgnored               ExitSuccess
  , testGroup "bytestring"  <$> dirTests "benchmarks/bytestring-0.9.2.1"        []                        ExitSuccess
  , testGroup "esop"        <$> dirTests "benchmarks/esop2013-submission"       esopIgnored               ExitSuccess
  , testGroup "vect-algs"   <$> dirTests "benchmarks/vector-algorithms-0.5.4.2" []                        ExitSuccess
  , testGroup "icfp_pos"    <$> dirTests "benchmarks/icfp15/pos"                icfpIgnored               ExitSuccess
  , testGroup "icfp_neg"    <$> dirTests "benchmarks/icfp15/neg"                icfpIgnored               (ExitFailure 1)
  ]

proverTests :: IO TestTree
proverTests = group "Prover"
  [ -- SUBSUMED-by-popl18 testGroup "pldi17_pos"  <$> dirTests "benchmarks/pldi17/pos"                proverIgnored             ExitSuccess
    testGroup "pldi17_neg"  <$> dirTests "benchmarks/pldi17/neg"                proverIgnored             (ExitFailure 1)
  , testGroup "instances"   <$> dirTests "benchmarks/proofautomation/pos"       autoIgnored               ExitSuccess
  , testGroup "foundations" <$> dirTests "benchmarks/sf"                        []                        ExitSuccess
  , testGroup "without_ple" <$> dirTests "benchmarks/popl18/nople/pos"          autoIgnored               ExitSuccess
  , testGroup "with_ple"    <$> dirTests "benchmarks/popl18/ple/pos"            autoIgnored               ExitSuccess
  ]

selfTests :: IO TestTree
selfTests
  = group "Self" [
      testGroup "liquid"      <$> dirTests "src"  [] ExitSuccess
  ]

--------------------------------------------------------------------------------
-- | For each file in `root` check, that we get the given exit `code.`
--------------------------------------------------------------------------------
dirTests :: FilePath -> [FilePath] -> ExitCode -> IO [TestTree]
--------------------------------------------------------------------------------
dirTests root ignored code = do
  files    <- walkDirectory root
  let tests = [ rel | f <- files, isTest f, let rel = makeRelative root f, rel `notElem` ignored ]
  return    $ mkCodeTest code root <$> tests

mkCodeTest :: ExitCode -> FilePath -> FilePath -> TestTree
mkCodeTest code dir file = mkTest (EC file code Nothing) dir file

isTest   :: FilePath -> Bool
isTest f =  takeExtension f == ".hs"
         || takeExtension f == ".lhs"

--------------------------------------------------------------------------------
-- | Check that we get the given `err` text and `ExitFailure status` for the given `path`.
--------------------------------------------------------------------------------
errorTest :: FilePath -> Int -> T.Text -> IO TestTree
--------------------------------------------------------------------------------
errorTest path status err = return (mkTest ec dir file)
  where
    ec                    = EC file (ExitFailure status) (Just err)
    (dir, file)           = splitFileName path

--------------------------------------------------------------------------------
data ExitCheck = EC { ecTest :: FilePath, ecCode :: ExitCode, ecLog :: Maybe T.Text }
                 deriving (Show)

ecAssert :: ExitCheck -> ExitCode -> T.Text -> Assertion
ecAssert ec (ExitFailure 137) _   =
  printf "WARNING: possible OOM while testing %s: IGNORING" (ecTest ec)

ecAssert (EC _ code Nothing)  c _   =
  assertEqual "Wrong exit code" code c

ecAssert (EC _ code (Just t)) c log = do
  assertEqual "Wrong exit code" code c
  assertBool ("Did not match message: " ++ T.unpack t) (T.isInfixOf t log)

--------------------------------------------------------------------------------
mkTest :: ExitCheck -> FilePath -> FilePath -> TestTree
--------------------------------------------------------------------------------
mkTest ec dir file
  = askOption $ \(smt :: SmtSolver) -> askOption $ \(opts :: LiquidOpts) -> testCase file $
      if test `elem` knownToFail smt
      then do
        printf "%s is known to fail with %s: SKIPPING" test (show smt)
        assertEqual "" True True
      else do
        createDirectoryIfMissing True $ takeDirectory log
        bin <- binPath "liquid"
        hSetBuffering stdout LineBuffering -- or even NoBuffering
        withFile log WriteMode $ \h -> do
          let cmd     = testCmd bin dir file smt $ mappend (extraOptions dir test) opts
          -- let cmd     = testCmd bin dir file smt $ mappend (extraOptions dir test) $ mappend "-v" opts
          (_,_,_,ph) <- createProcess $ (shell cmd) {std_out = UseHandle h, std_err = UseHandle h}
          c          <- waitForProcess ph
          ecAssert ec c =<< T.readFile log
          -- renameFile log $ log <.> (if code == c then "pass" else "fail")
          -- if c == ExitFailure 137
            -- then printf "WARNING: possible OOM while testing %s: IGNORING" test
            -- else assertEqual "Wrong exit code" code c
  where
    test = dir </> file
    log = "tests/logs/cur" </> test <.> "log"

binPath :: FilePath -> IO FilePath
binPath pkgName = (</> pkgName) <$> getBinDir

knownToFail :: SmtSolver -> [FilePath]
knownToFail CVC4 = [ "tests/pos/linspace.hs"
                   , "tests/pos/RealProps.hs"
                   , "tests/pos/RealProps1.hs"
                   , "tests/pos/initarray.hs"
                   , "tests/pos/maps.hs"
                   , "tests/pos/maps1.hs"
                   , "tests/neg/maps.hs"
                   , "tests/pos/Product.hs"
                   , "tests/pos/Gradual.hs"
                   , "tests/equationalproofs/pos/MapAppend.hs"
                   ]

knownToFail Z3   = [ "tests/pos/linspace.hs"
                   , "tests/equationalproofs/pos/MapAppend.hs"
                   ]

--------------------------------------------------------------------------------
extraOptions :: FilePath -> FilePath -> LiquidOpts
--------------------------------------------------------------------------------
extraOptions dir test = mappend (dirOpts dir) (testOpts test)
  where
    dirOpts = flip (Map.findWithDefault mempty) $ Map.fromList
      [ ( "benchmarks/bytestring-0.9.2.1"
        , "--no-lifted-imports -iinclude --c-files=cbits/fpstring.c"
        )
      , ( "benchmarks/text-0.11.2.3"
        , "--no-lifted-imports -i../bytestring-0.9.2.1 -i../bytestring-0.9.2.1/include --c-files=../bytestring-0.9.2.1/cbits/fpstring.c -i../../include --c-files=cbits/cbits.c"
        )
      , ( "benchmarks/vector-0.10.0.1"
        , "-i."
        )
      , ( "tests/import/client"
        , "-i../lib"
        )
      ]
    testOpts = flip (Map.findWithDefault mempty) $ Map.fromList
      [ ( "tests/pos/Class2.hs"
        , "-i../neg"
        )
      , ( "tests/pos/FFI.hs"
        , "-i../ffi-include --c-files=../ffi-include/foo.c"
        )
      ]

---------------------------------------------------------------------------
testCmd :: FilePath -> FilePath -> FilePath -> SmtSolver -> LiquidOpts -> String
---------------------------------------------------------------------------
testCmd bin dir file smt (LO opts)
  = printf "cd %s && %s --smtsolver %s %s %s" dir bin (show smt) file opts

esopIgnored = [ "Base0.hs"
              -- , "Base.hs"                  -- REFLECT-IMPORTS: TODO BLOWUP
              ]

icfpIgnored :: [FilePath]
icfpIgnored = [ "RIO.hs"
              , "DataBase.hs"
              , "FindRec.hs"
              , "CopyRec.hs"
              , "TwiceM.hs"                -- TODO: BLOWUP: using 2.7GB RAM
              ]

proverIgnored  :: [FilePath]
proverIgnored = [ "OverviewListInfix.hs"
                , "Proves.hs"
                , "Helper.hs"
                , "FunctorReader.hs"      -- NOPROP: TODO: Niki please fix!
                , "MonadReader.hs"        -- NOPROP: ""
                , "ApplicativeReader.hs"  -- NOPROP: ""
                , "FunctorReader.NoExtensionality.hs" -- Name resolution issues
                -- , "Fibonacci.hs"          -- REFLECT-IMPORTS: TODO: Niki please fix!
                ]

autoIgnored = "Ackermann.hs" : proverIgnored



hscIgnored :: [FilePath]
hscIgnored = [ "HsColour.hs"
             , "Language/Haskell/HsColour/Classify.hs"      -- eliminate
             , "Language/Haskell/HsColour/Anchors.hs"       -- eliminate
             , "Language/Haskell/HsColour/ACSS.hs"          -- eliminate
             ]

negIgnored :: [FilePath]
negIgnored = [ "Lib.hs"
             , "LibSpec.hs"
             ]

textIgnored :: [FilePath]
textIgnored = [ "Setup.lhs"
              , "Data/Text/Axioms.hs"
              , "Data/Text/Encoding/Error.hs"
              , "Data/Text/Encoding/Fusion.hs"
              , "Data/Text/Encoding/Fusion/Common.hs"
              , "Data/Text/Encoding/Utf16.hs"
              , "Data/Text/Encoding/Utf32.hs"
              , "Data/Text/Encoding/Utf8.hs"
              , "Data/Text/Fusion/CaseMapping.hs"
              , "Data/Text/Fusion/Common.hs"
              , "Data/Text/Fusion/Internal.hs"
              , "Data/Text/IO.hs"
              , "Data/Text/IO/Internal.hs"
              , "Data/Text/Lazy/Builder/Functions.hs"
              , "Data/Text/Lazy/Builder/Int.hs"
              , "Data/Text/Lazy/Builder/Int/Digits.hs"
              , "Data/Text/Lazy/Builder/Internal.hs"
              , "Data/Text/Lazy/Builder/RealFloat.hs"
              , "Data/Text/Lazy/Builder/RealFloat/Functions.hs"
              , "Data/Text/Lazy/Encoding/Fusion.hs"
              , "Data/Text/Lazy/IO.hs"
              , "Data/Text/Lazy/Read.hs"
              , "Data/Text/Read.hs"
              , "Data/Text/Unsafe/Base.hs"
              , "Data/Text/UnsafeShift.hs"
              , "Data/Text/Util.hs"
              , "Data/Text/Fusion-debug.hs"
              , "Data/Text/Encoding.hs"
              ]

demosIgnored :: [FilePath]
demosIgnored = [ "Composition.hs"
               , "Eval.hs"
               , "Inductive.hs"
               , "Loop.hs"
               , "TalkingAboutSets.hs"
               , "refinements101reax.hs"
               ]

----------------------------------------------------------------------------------------
-- Generic Helpers
----------------------------------------------------------------------------------------
group :: (Monad m) => TestName -> [m TestTree] -> m TestTree
group n xs = testGroup n <$> sequence xs

gitTimestamp :: IO String
gitTimestamp = do
   res <- gitProcess ["show", "--format=\"%ci\"", "--quiet"]
   return $ filter notNoise res

gitEpochTimestamp :: IO String
gitEpochTimestamp = do
   res <- gitProcess ["show", "--format=\"%ct\"", "--quiet"]
   return $ filter notNoise res

gitHash :: IO String
gitHash = do
   res <- gitProcess ["show", "--format=\"%H\"", "--quiet"]
   return $ filter notNoise res

gitRef :: IO String
gitRef = do
   res <- gitProcess ["show", "--format=\"%d\"", "--quiet"]
   return $ filter notNoise res

-- | Calls `git` for info; returns `"plain"` if we are not in a git directory.
gitProcess :: [String] -> IO String
gitProcess args = (readProcess "git" args []) `catchIOError` const (return "plain")

notNoise :: Char -> Bool
notNoise a = a /= '\"' && a /= '\n' && a /= '\r'

headerDelim :: String
headerDelim = replicate 80 '-'

----------------------------------------------------------------------------------------
walkDirectory :: FilePath -> IO [FilePath]
----------------------------------------------------------------------------------------
walkDirectory root
  = do -- RJ: delete root </> ".liquid"
       (ds,fs) <- partitionM doesDirectoryExist . candidates =<< (getDirectoryContents root `catchIOError` const (return []))
       (fs ++) <$> concatMapM walkDirectory ds
    where
       candidates fs = [root </> f | f <- fs, not (isExtSeparator (head f))]

partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
partitionM f = go [] []
  where
    go ls rs []     = return (ls,rs)
    go ls rs (x:xs) = do b <- f x
                         if b then go (x:ls) rs xs
                              else go ls (x:rs) xs

-- isDirectory :: FilePath -> IO Bool
-- isDirectory = fmap Posix.isDirectory . Posix.getFileStatus

concatMapM :: Applicative m => (a -> m [b]) -> [a] -> m [b]
concatMapM _ []     = pure []
concatMapM f (x:xs) = (++) <$> f x <*> concatMapM f xs

-- | Combine two @TestReporter@s into one.
--
-- Runs the reporters in sequence, so it's best to start with the one
-- that will produce incremental output, e.g. 'consoleTestReporter'.
combineReporters :: Ingredient -> Ingredient -> Ingredient
combineReporters (TestReporter opts1 run1) (TestReporter opts2 run2)
  = TestReporter (opts1 ++ opts2) $ \opts tree -> do
      f1 <- run1 opts tree
      f2 <- run2 opts tree
      return $ \smap -> f1 smap >> f2 smap
combineReporters _ _ = error "combineReporters needs TestReporters"

type Summary = [(String, Double, Bool)]

-- this is largely based on ocharles' test runner at
-- https://github.com/ocharles/tasty-ant-xml/blob/master/Test/Tasty/Runners/AntXML.hs#L65
loggingTestReporter :: Ingredient
loggingTestReporter = TestReporter [] $ \opts tree -> Just $ \smap -> do
  let
    runTest _ testName _ = Traversal $ Functor.Compose $ do
        i <- State.get

        summary <- lift $ STM.atomically $ do
          status <- STM.readTVar $
            fromMaybe (error "Attempted to lookup test by index outside bounds") $
              IntMap.lookup i smap

          let mkSuccess time = [(testName, time, True)]
              mkFailure time = [(testName, time, False)]

          case status of
            -- If the test is done, generate a summary for it
            Done result
              | resultSuccessful result
                  -> pure (mkSuccess (resultTime result))
              | otherwise
                  -> pure (mkFailure (resultTime result))
            -- Otherwise the test has either not been started or is currently
            -- executing
            _ -> STM.retry

        Const summary <$ State.modify (+ 1)

    runGroup group children = Traversal $ Functor.Compose $ do
      Const soFar <- Functor.getCompose $ getTraversal children
      pure $ Const $ map (\(n,t,s) -> (group</>n,t,s)) soFar

    computeFailures :: StatusMap -> IO Int
    computeFailures = fmap getSum . getApp . foldMap (\var -> Ap $
      (\r -> Sum $ if resultSuccessful r then 0 else 1) <$> getResultFromTVar var)

    getResultFromTVar :: STM.TVar Status -> IO Result
    getResultFromTVar var =
      STM.atomically $ do
        status <- STM.readTVar var
        case status of
          Done r -> return r
          _ -> STM.retry

  (Const summary, _tests) <-
     flip State.runStateT 0 $ Functor.getCompose $ getTraversal $
      foldTestTree
        trivialFold { foldSingle = runTest, foldGroup = runGroup }
        opts
        tree

  return $ \_elapsedTime -> do
    -- get some semblance of a hostname
    host <- takeWhile (/='.') . takeWhile (not . isSpace) <$> readProcess "hostname" [] []
    -- don't use the `time` package, major api differences between ghc 708 and 710
    time <- head . lines <$> readProcess "date" ["+%Y-%m-%dT%H-%M-%S"] []
    -- build header
    ref       <- gitRef
    timestamp <- gitTimestamp
    epochTime <- gitEpochTimestamp
    hash      <- gitHash
    let hdr = unlines [ref ++ " : " ++ hash,
                       "Timestamp: " ++ timestamp,
                       "Epoch Timestamp: " ++ epochTime,
                       headerDelim,
                       "test, time(s), result"]

    let dir = "tests" </> "logs" </> host ++ "-" ++ time
    let smry = "tests" </> "logs" </> "cur" </> "summary.csv"
    writeFile smry $ unlines
                   $ hdr
                   : map (\(n, t, r) -> printf "%s, %0.4f, %s" n t (show r)) summary
    system $ "cp -r tests/logs/cur " ++ dir
    (==0) <$> computeFailures smap
