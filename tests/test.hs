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
import Data.Monoid (Sum(..))
import Data.Proxy
import Data.String
import Data.Tagged
import Data.Typeable
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
    tests = group "Tests" [ unitTests, benchTests ]
    -- tests = group "Tests" [ benchTests ]
    -- tests = group "Tests" [ selfTests ]

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

unitTests :: IO TestTree
unitTests
  = group "Unit" [
      testGroup "pos"         <$> dirTests "tests/pos"                            []           ExitSuccess
    , testGroup "neg"         <$> dirTests "tests/neg"                            negIgnored   (ExitFailure 1)
    , testGroup "crash"       <$> dirTests "tests/crash"                          []           (ExitFailure 2)
    , testGroup "parser/pos"  <$> dirTests "tests/parser/pos"                     []           ExitSuccess
    , testGroup "error/crash" <$> dirTests "tests/error_messages/crash"           []           (ExitFailure 2)
    -- , testGroup "eq_pos"      <$> dirTests "tests/equationalproofs/pos"           ["Axiomatize.hs", "Equational.hs"]           ExitSuccess
    -- , testGroup "eq_neg"      <$> dirTests "tests/equationalproofs/neg"           ["Axiomatize.hs", "Equational.hs"]           (ExitFailure 1)
   ]

benchTests :: IO TestTree
benchTests
  = group "Benchmarks" [
       testGroup "text"        <$> dirTests "benchmarks/text-0.11.2.3"             textIgnored               ExitSuccess
     , testGroup "bytestring"  <$> dirTests "benchmarks/bytestring-0.9.2.1"        []                        ExitSuccess
     , testGroup "esop"        <$> dirTests "benchmarks/esop2013-submission"       ["Base0.hs"]              ExitSuccess
     , testGroup "vect-algs"   <$> dirTests "benchmarks/vector-algorithms-0.5.4.2" []                        ExitSuccess
     , testGroup "hscolour"    <$> dirTests "benchmarks/hscolour-1.20.0.0"         hscIgnored                ExitSuccess
     , testGroup "icfp_pos"    <$> dirTests "benchmarks/icfp15/pos"                icfpIgnored               ExitSuccess
     , testGroup "icfp_neg"    <$> dirTests "benchmarks/icfp15/neg"                icfpIgnored               (ExitFailure 1)
     , testGroup "popl17_pos"   <$> dirTests "benchmarks/popl17/pos"         proverIgnored             ExitSuccess
     , testGroup "popl17_neg"   <$> dirTests "benchmarks/popl17/neg"         proverIgnored             (ExitFailure 1)
     ]

selfTests :: IO TestTree
selfTests
  = group "Self" [
      testGroup "liquid"      <$> dirTests "src"  [] ExitSuccess
  ]

---------------------------------------------------------------------------
dirTests :: FilePath -> [FilePath] -> ExitCode -> IO [TestTree]
---------------------------------------------------------------------------
dirTests root ignored code
  = do files    <- walkDirectory root
       let tests = [ rel | f <- files, isTest f, let rel = makeRelative root f, rel `notElem` ignored ]
       return    $ mkTest code root <$> tests

isTest   :: FilePath -> Bool
isTest f =  takeExtension f == ".hs"
         || takeExtension f == ".lhs"

---------------------------------------------------------------------------
mkTest :: ExitCode -> FilePath -> FilePath -> TestTree
---------------------------------------------------------------------------
mkTest code dir file
  = askOption $ \(smt :: SmtSolver) -> askOption $ \(opts :: LiquidOpts) -> testCase file $
      if test `elem` knownToFail smt
      then do
        printf "%s is known to fail with %s: SKIPPING" test (show smt)
        assertEqual "" True True
      else do
        createDirectoryIfMissing True $ takeDirectory log
        bin <- binPath "liquid"
        withFile log WriteMode $ \h -> do
          let cmd     = testCmd bin dir file smt $ mappend (extraOptions dir test) opts
          (_,_,_,ph) <- createProcess $ (shell cmd) {std_out = UseHandle h, std_err = UseHandle h}
          c          <- waitForProcess ph
          renameFile log $ log <.> (if code == c then "pass" else "fail")
          if c == ExitFailure 137
            then printf "WARNING: possible OOM while testing %s: IGNORING" test
            else assertEqual "Wrong exit code" code c
  where
    test = dir </> file
    log = "tests/logs/cur" </> test <.> "log"

binPath :: FilePath -> IO FilePath
binPath pkgName = do
  testPath <- getExecutablePath
  return    $ takeDirectory (takeDirectory testPath) </> pkgName </> pkgName

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
                   , "tests/pos/Gradual.hs"
                   , "tests/equationalproofs/pos/MapAppend.hs"
                   ]

--------------------------------------------------------------------------------
extraOptions :: FilePath -> FilePath -> LiquidOpts
--------------------------------------------------------------------------------
extraOptions dir test = mappend (dirOpts dir) (testOpts test)
  where
    dirOpts = flip (Map.findWithDefault mempty) $ Map.fromList
      [ ( "benchmarks/bytestring-0.9.2.1"
        , "-iinclude --c-files=cbits/fpstring.c"
        )
      , ( "benchmarks/text-0.11.2.3"
        , "-i../bytestring-0.9.2.1 -i../bytestring-0.9.2.1/include --c-files=../bytestring-0.9.2.1/cbits/fpstring.c -i../../include --c-files=cbits/cbits.c"
        )
      , ( "benchmarks/vector-0.10.0.1"
        , "-i."
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

icfpIgnored :: [FilePath]
icfpIgnored = [ "RIO.hs"
              , "DataBase.hs" 
              ]

proverIgnored  :: [FilePath]
proverIgnored = [ "OverviewListInfix.hs"
                , "Proves.hs"
                , "Helper.hs"
                , "ApplicativeList.hs"
                ]


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
textIgnored = [ "Data/Text/Axioms.hs"
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
   res <- readProcess "git" ["show", "--format=\"%ci\"", "--quiet"] []
   return $ filter notNoise res

gitEpochTimestamp :: IO String
gitEpochTimestamp = do
   res <- readProcess "git" ["show", "--format=\"%ct\"", "--quiet"] []
   return $ filter notNoise res

gitHash :: IO String
gitHash = do
   res <- readProcess "git" ["show", "--format=\"%H\"", "--quiet"] []
   return $ filter notNoise res

gitRef :: IO String
gitRef = do
   res <- readProcess "git" ["show", "--format=\"%d\"", "--quiet"] []
   return $ filter notNoise res

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
    ref <- gitRef
    timestamp <- gitTimestamp
    epochTime <- gitEpochTimestamp
    hash <- gitHash
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
