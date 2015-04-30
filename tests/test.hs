{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

-- import Language.Fixpoint.Config
-- import Language.Fixpoint.Names
-- import Language.Fixpoint.Parse
-- import Language.Fixpoint.PrettyPrint
-- import Language.Fixpoint.Types

import Control.Applicative
-- import Data.Char
-- import Data.Tagged
-- import Data.Typeable
-- import Options.Applicative
import System.Directory
import System.Exit
import System.FilePath
import System.IO
-- import qualified System.Posix as Posix
import System.Process

-- import Control.Monad
-- import Data.Proxy
-- import Data.Text (Text, cons, inits, pack)
-- import Test.QuickCheck
import Test.Tasty
import Test.Tasty.HUnit
-- import Test.Tasty.Ingredients.Rerun
-- import Test.Tasty.Options
-- import Test.Tasty.QuickCheck
-- import Test.Tasty.Runners
import Text.Printf

main :: IO ()
main = defaultMain =<< tests
  where
    tests = group "Tests" [unitTests] -- [ quickCheckTests ]
    -- run   = defaultMainWithIngredients [
    --             rerunningTests   [ listingTests, consoleTestReporter ]
    --           , includingOptions [ Option (Proxy :: Proxy QuickCheckTests)
    --                              ]
    --           ]


unitTests
  = group "Unit" [
      testGroup "pos" <$> dirTests "tests/pos" []  ExitSuccess
    , testGroup "neg" <$> dirTests "tests/neg" []  (ExitFailure 1)
   ]

---------------------------------------------------------------------------
dirTests :: FilePath -> [FilePath] -> ExitCode -> IO [TestTree]
---------------------------------------------------------------------------
dirTests root ignored code
  = do files    <- walkDirectory root
       let tests = [ rel | f <- files, isTest f, let rel = makeRelative root f, rel `notElem` ignored ]
       return    $ mkTest code root <$> tests --  hs f code | f <- hs]

isTest   :: FilePath -> Bool
isTest f = takeExtension f `elem` [".fq"]

---------------------------------------------------------------------------
mkTest :: ExitCode -> FilePath -> FilePath -> TestTree
---------------------------------------------------------------------------
mkTest code dir file
  = -- askOption $ \(smt :: SMTSolver) ->
    testCase file $
      if test `elem` knownToFail
      then do
        printf "%s is known to fail: SKIPPING" test
        assertEqual "" True True
      else do
        createDirectoryIfMissing True $ takeDirectory log
        bin <- canonicalizePath ".cabal-sandbox/bin/fixpoint"
        withFile log WriteMode $ \h -> do
          let cmd     = testCmd bin dir file
          (_,_,_,ph) <- createProcess $ (shell cmd) {std_out = UseHandle h, std_err = UseHandle h}
          c          <- waitForProcess ph
          assertEqual "Wrong exit code" code c
  where
    test = dir </> file
    log  = let (d,f) = splitFileName file in dir </> d </> ".liquid" </> f <.> "log"

knownToFail = []

---------------------------------------------------------------------------
testCmd :: FilePath -> FilePath -> FilePath -> String
---------------------------------------------------------------------------
testCmd bin dir file = printf "cd %s && %s -n %s" dir bin file















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
  = do (ds,fs) <- partitionM doesDirectoryExist . candidates =<< getDirectoryContents root
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
