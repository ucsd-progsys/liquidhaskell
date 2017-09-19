{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import qualified Control.Concurrent.STM as STM
import qualified Data.Functor.Compose   as Functor
import qualified Data.IntMap            as IntMap
import qualified Data.Map               as Map
import qualified Control.Monad.State    as State
import Control.Monad.Trans.Class (lift)

import Data.Char
import Data.Maybe (fromMaybe)
import Data.Monoid (Sum(..), (<>))
import Control.Applicative
import System.Directory
import System.Exit
import System.FilePath
import System.Environment
import System.IO
import System.IO.Error
import System.Process
import Text.Printf

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Ingredients.Rerun
import Test.Tasty.Options
import Test.Tasty.Runners
import Test.Tasty.Runners.AntXML
import Paths_liquid_fixpoint

main :: IO ()
main    = run =<< group "Tests" [unitTests]
  where
    run = defaultMainWithIngredients [
                testRunner
            --  , includingOptions [ Option (Proxy :: Proxy NumThreads)
            --                     , Option (Proxy :: Proxy LiquidOpts)
            --                     , Option (Proxy :: Proxy SmtSolver) ]
              ]

testRunner :: Ingredient
testRunner = rerunningTests
               [ listingTests
               , combineReporters myConsoleReporter antXMLRunner
               , myConsoleReporter
               ]

myConsoleReporter :: Ingredient
myConsoleReporter = combineReporters consoleTestReporter loggingTestReporter

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

unitTests
  = group "Unit" [
      testGroup "native-pos" <$> dirTests nativeCmd "tests/pos"    skipNativePos  ExitSuccess
    , testGroup "native-neg" <$> dirTests nativeCmd "tests/neg"    ["float.fq"]   (ExitFailure 1)
    , testGroup "elim-crash" <$> dirTests nativeCmd "tests/crash"  []             (ExitFailure 2)
    , testGroup "elim-pos1"  <$> dirTests elimCmd   "tests/pos"    []             ExitSuccess
    , testGroup "elim-pos2"  <$> dirTests elimCmd   "tests/elim"   []             ExitSuccess
    , testGroup "elim-neg"   <$> dirTests elimCmd   "tests/neg"    ["float.fq"]   (ExitFailure 1)
    , testGroup "elim-crash" <$> dirTests elimCmd   "tests/crash"  []             (ExitFailure 2)
    , testGroup "proof"      <$> dirTests elimCmd   "tests/proof"  []             ExitSuccess
    , testGroup "todo"       <$> dirTests elimCmd   "tests/todo"   ["LH1090.fq"]  (ExitFailure 2)
   ]

skipNativePos :: [FilePath]
skipNativePos = ["NonLinear-pack.fq"]

---------------------------------------------------------------------------
dirTests :: TestCmd -> FilePath -> [FilePath] -> ExitCode -> IO [TestTree]
---------------------------------------------------------------------------
dirTests testCmd root ignored code
  = do files    <- walkDirectory root
       let tests = [ rel | f <- files, isTest f, let rel = makeRelative root f, rel `notElem` ignored ]
       return    $ mkTest testCmd code root <$> tests

isTest   :: FilePath -> Bool
isTest f = takeExtension f `elem` [".fq"]

---------------------------------------------------------------------------
mkTest :: TestCmd -> ExitCode -> FilePath -> FilePath -> TestTree
---------------------------------------------------------------------------
mkTest testCmd code dir file
  = testCase file $
      if test `elem` knownToFail
      then do
        printf "%s is known to fail: SKIPPING" test
        assertEqual "" True True
      else do
        createDirectoryIfMissing True $ takeDirectory log
        bin <- binPath "fixpoint"
        withFile log WriteMode $ \h -> do
          let cmd     = testCmd bin dir file
          (_,_,_,ph) <- createProcess $ (shell cmd) {std_out = UseHandle h, std_err = UseHandle h}
          c          <- waitForProcess ph
          assertEqual "Wrong exit code" code c
  where
    test = dir </> file
    log  = let (d,f) = splitFileName file in dir </> d </> ".liquid" </> f <.> "log"

binPath :: FilePath -> IO FilePath
binPath pkgName = (</> pkgName) <$> getBinDir

knownToFail = []
---------------------------------------------------------------------------
type TestCmd = FilePath -> FilePath -> FilePath -> String

nativeCmd :: TestCmd
nativeCmd bin dir file = printf "cd %s && %s %s" dir bin file

elimCmd :: TestCmd
elimCmd bin dir file = printf "cd %s && %s --eliminate=some %s" dir bin file















---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

{-

quickCheckTests :: TestTree
quickCheckTests
  = testGroup "Properties"
      [ testProperty "prop_pprint_parse_inv_expr" prop_pprint_parse_inv_expr
      , testProperty "prop_pprint_parse_inv_pred" prop_pprint_parse_inv_pred
      ]

prop_pprint_parse_inv_pred :: Pred -> Bool
prop_pprint_parse_inv_pred p = p == rr (showpp p)

prop_pprint_parse_inv_expr :: Expr -> Bool
prop_pprint_parse_inv_expr p = simplify p == rr (showpp $ simplify p)

instance Arbitrary Sort where
  arbitrary = sized arbSort

arbSort 0 = oneof [return FInt, return FReal, return FNum]
arbSort n = frequency
              [(1, return FInt)
              ,(1, return FReal)
              ,(1, return FNum)
              ,(2, fmap FObj arbitrary)
              ]


instance Arbitrary Pred where
  arbitrary = sized arbPred
  shrink = filter valid . genericShrink
    where
      valid (PAnd [])  = False
      valid (PAnd [_]) = False
      valid (POr [])   = False
      valid (POr [_])  = False
      valid (PBexp (EBin _ _ _)) = True
      valid (PBexp _)  = False
      valid _          = True

arbPred 0 = elements [PTrue, PFalse]
arbPred n = frequency
              [(1, return PTrue)
              ,(1, return PFalse)
              ,(2, fmap PAnd  twoPreds)
              ,(2, fmap POr   twoPreds)
              ,(2, fmap PNot (arbPred (n `div` 2)))
              ,(2, liftM2 PImp (arbPred (n `div` 2)) (arbPred (n `div` 2)))
              ,(2, liftM2 PIff (arbPred (n `div` 2)) (arbPred (n `div` 2)))
              ,(2, fmap PBexp (arbExpr (n `div` 2)))
              ,(2, liftM3 PAtom arbitrary (arbExpr (n `div` 2)) (arbExpr (n `div` 2)))
              -- ,liftM2 PAll arbitrary arbitrary
              -- ,return PTop
              ]
  where
    twoPreds = do
      x <- arbPred (n `div` 2)
      y <- arbPred (n `div` 2)
      return [x,y]

instance Arbitrary Expr where
  arbitrary = sized arbExpr
  shrink = filter valid . genericShrink
    where valid (EApp _ []) = False
          valid _           = True

arbExpr 0 = oneof [fmap ESym arbitrary, fmap ECon arbitrary, fmap EVar arbitrary, return EBot]
arbExpr n = frequency
              [(1, fmap ESym arbitrary)
              ,(1, fmap ECon arbitrary)
              ,(1, fmap EVar arbitrary)
              ,(1, return EBot)
              -- ,liftM2 ELit arbitrary arbitrary -- restrict literals somehow
              ,(2, choose (1,3) >>= \m -> liftM2 EApp arbitrary (vectorOf m (arbExpr (n `div` 2))))
              ,(2, liftM3 EBin arbitrary (arbExpr (n `div` 2)) (arbExpr (n `div` 2)))
              ,(2, liftM3 EIte (arbPred (max 2 (n `div` 2)) `suchThat` isRel)
                               (arbExpr (n `div` 2))
                               (arbExpr (n `div` 2)))
              ,(2, liftM2 ECst (arbExpr (n `div` 2)) (arbSort (n `div` 2)))
              ]
  where
    isRel (PAtom _ _ _) = True
    isRel _             = False

instance Arbitrary Brel where
  arbitrary = oneof (map return [Eq, Ne, Gt, Ge, Lt, Le, Ueq, Une])

instance Arbitrary Bop where
  arbitrary = oneof (map return [Plus, Minus, Times, Div, Mod])

instance Arbitrary SymConst where
  arbitrary = fmap SL arbitrary

instance Arbitrary Symbol where
  arbitrary = fmap (symbol :: Text -> Symbol) arbitrary

instance Arbitrary Text where
  arbitrary = choose (1,4) >>= \n ->
                fmap pack (vectorOf n char `suchThat` valid)
    where
      char = elements ['a'..'z']
      valid x = x `notElem` fixpointNames && not (isFixKey x)

instance Arbitrary FTycon where
  arbitrary = do
    c <- elements ['A'..'Z']
    t <- arbitrary
    return $ symbolFTycon $ dummyLoc $ symbol $ cons c t

instance Arbitrary Constant where
  arbitrary = oneof [fmap I (arbitrary `suchThat` (>=0))
                    -- ,fmap R arbitrary
                    ]
  shrink = genericShrink

instance Arbitrary a => Arbitrary (Located a) where
  arbitrary = fmap dummyLoc arbitrary
  shrink = fmap dummyLoc . shrink . val

-}

----------------------------------------------------------------------------------------
-- Generic Helpers
----------------------------------------------------------------------------------------

group n xs = testGroup n <$> sequence xs

----------------------------------------------------------------------------------------
walkDirectory :: FilePath -> IO [FilePath]
----------------------------------------------------------------------------------------
walkDirectory root
  = do (ds,fs) <- partitionM doesDirectoryExist . candidates =<< (getDirectoryContents root `catchIOError` const (return []))
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

-- isDirectory :: FilePath -> IO Bool
-- isDirectory = fmap Posix.isDirectory . Posix.getFileStatus

concatMapM :: Applicative m => (a -> m [b]) -> [a] -> m [b]
concatMapM _ []     = pure []
concatMapM f (x:xs) = (++) <$> f x <*> concatMapM f xs



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
    -- system $ "cp -r tests/logs/cur " ++ dir
    (==0) <$> computeFailures smap


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
