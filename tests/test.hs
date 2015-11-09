{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Control.Applicative
import System.Directory
import System.Exit
import System.FilePath
import System.Environment
import System.IO
import System.IO.Error
import System.Process
import Test.Tasty
import Test.Tasty.HUnit
import Text.Printf

main :: IO ()
main = defaultMain =<< group "Tests" [unitTests]

unitTests
  = group "Unit" [
      testGroup "native-pos" <$> dirTests nativeCmd "tests/pos"  []  ExitSuccess
    , testGroup "native-neg" <$> dirTests nativeCmd "tests/neg"  []  (ExitFailure 1)
    , testGroup "elim-pos1"  <$> dirTests elimCmd   "tests/pos"  []  ExitSuccess
    , testGroup "elim-pos2"  <$> dirTests elimCmd   "tests/elim" []  ExitSuccess
    , testGroup "elim-neg"   <$> dirTests elimCmd   "tests/neg"  []  (ExitFailure 1)
   ]

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

binPath pkgName = do
  testPath <- getExecutablePath
  return    $ (takeDirectory $ takeDirectory testPath) </> pkgName </> pkgName

knownToFail = []
---------------------------------------------------------------------------
type TestCmd = FilePath -> FilePath -> FilePath -> String

nativeCmd :: TestCmd
nativeCmd bin dir file = printf "cd %s && %s %s" dir bin file

elimCmd :: TestCmd
elimCmd bin dir file = printf "cd %s && %s --eliminate %s" dir bin file















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
