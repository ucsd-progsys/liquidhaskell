module Main where

import Control.Applicative
import Control.Monad
import System.Directory
import System.Exit
import System.FilePath
import System.IO
import qualified System.Posix as Posix
import System.Process
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Ingredients.Rerun
import Test.Tasty.Runners
import Text.Printf

main :: IO ()
main
  = do pos <- dirTests "tests/pos" [] ExitSuccess
       neg <- dirTests "tests/neg" [] (ExitFailure 1)
       crash <- dirTests "tests/crash" [] (ExitFailure 2)
       -- benchmarks
       text <- dirTests "benchmarks/text-0.11.2.3" textIgnored ExitSuccess
       bs <- dirTests "benchmarks/bytestring-0.9.2.1" [] ExitSuccess
       esop <- dirTests "benchmarks/esop2013-submission" ["Base0.hs"] ExitSuccess
       vector_algs <- dirTests "benchmarks/vector-algorithms-0.5.4.2" [] ExitSuccess
       hscolour <- dirTests "benchmarks/hscolour-1.20.0.0" [] ExitSuccess
       -- TestTrees
       let unit = testGroup "Unit"
                    [ testGroup "pos" pos
                    , testGroup "neg" neg
                    , testGroup "crash" crash
                    ]
       let bench = testGroup "Benchmarks"
                     [ testGroup "text" text
                     , testGroup "bytestring" bs
                     , testGroup "esop" esop
                     , testGroup "vector-algorithms" vector_algs
                     , testGroup "hscolour" hscolour
                     ]
       defaultMainWithIngredients
         [ rerunningTests [listingTests, consoleTestReporter] ]
         $ testGroup "Tests" [unit, bench]


mkTest :: FilePath -> FilePath -> ExitCode -> TestTree
mkTest dir file code
  = testCase rel $ withFile log WriteMode $ \h -> do
      let proc    = (shell $ mkCmd dir rel) {std_out = UseHandle h, std_err = UseHandle h}
      (_,_,_,ph) <- createProcess proc
      c          <-  waitForProcess ph
      assertEqual "Wrong exit code" code c
  where rel = makeRelative dir file
        log = let (d,f) = splitFileName file in d </> ".liquid" </> f <.> "log"

dirTests :: FilePath -> [FilePath] -> ExitCode -> IO [TestTree]
dirTests root ignored code
  = do cleanup root
       fs    <- walkDirectory root
       let hs = [f | f <- fs, isHaskellFile f, f `notElem` ignored]
       return [mkTest root f code | f <- hs]

cleanup :: FilePath -> IO ()
cleanup dir
  = do b <- doesDirectoryExist lq
       when b $ removeDirectoryRecursive lq
       createDirectory lq
  where lq = dir </> ".liquid"

walkDirectory :: FilePath -> IO [FilePath]
walkDirectory root
  = do (ds,fs) <- partitionM isDirectory . candidates =<< getDirectoryContents root
       (fs++) <$> concatMapM walkDirectory ds
  where
    candidates fs = [root </> f | f <- fs, not (isExtSeparator (head f))]

partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
partitionM f = go [] []
  where
    go ls rs []     = return (ls,rs)
    go ls rs (x:xs) = do b <- f x
                         if b then go (x:ls) rs xs
                              else go ls (x:rs) xs

isDirectory :: FilePath -> IO Bool
isDirectory = fmap Posix.isDirectory . Posix.getFileStatus

concatMapM :: Applicative m => (a -> m [b]) -> [a] -> m [b]
concatMapM f []     = pure []
concatMapM f (x:xs) = (++) <$> f x <*> concatMapM f xs

isHaskellFile :: FilePath -> Bool
isHaskellFile f = takeExtension f == ".hs" -- `elem` [".hs", ".lhs"]

mkCmd :: FilePath -> FilePath -> String
mkCmd dir file = printf "cd %s && liquid --verbose %s" dir file

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
              ]

demosIgnored = [ "Composition.hs"
               , "Eval.hs"
               , "Inductive.hs"
               , "Loop.hs"
               , "TalkingAboutSets.hs"
               , "refinements101reax.hs"
               ]

