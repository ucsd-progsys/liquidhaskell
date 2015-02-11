{-# OPTIONS_GHC -fno-warn-orphans #-}
module Main where

import Language.Fixpoint.Parse
import Language.Fixpoint.PrettyPrint
import Language.Fixpoint.Types

import Control.Monad
import Data.Proxy
import Data.Text (Text, pack)
import Test.Tasty
import Test.Tasty.Ingredients.Rerun
import Test.Tasty.Options
import Test.Tasty.QuickCheck
import Test.Tasty.Runners

main :: IO ()
main = run tests 
  where
    run   = defaultMainWithIngredients [ 
                rerunningTests   [ listingTests, consoleTestReporter ]
              , includingOptions [ Option (Proxy :: Proxy QuickCheckTests)
                                 ]
              ]
    
    tests = testGroup "Tests" [ quickCheckTests ]

quickCheckTests :: TestTree
quickCheckTests
  = testGroup "Properties" [
      testProperty "prop_pprint_parse_inv" prop_pprint_parse_inv
    ]

prop_pprint_parse_inv :: Expr -> Bool
prop_pprint_parse_inv p = p == rr (showpp p)

instance Arbitrary Sort where
  arbitrary = oneof [return FInt
                    ,return FReal
                    ,return FNum
                    ,fmap FObj arbitrary
                    ,fmap FVar arbitrary
                    ,liftM2 FFunc arbitrary arbitrary
                    ,liftM2 FApp arbitrary arbitrary
                    ]
  shrink = genericShrink

instance Arbitrary Pred where
  arbitrary = oneof [return PTrue
                    ,return PFalse
                    ,fmap PAnd arbitrary
                    ,fmap POr arbitrary
                    ,fmap PNot arbitrary
                    ,liftM2 PImp arbitrary arbitrary
                    ,liftM2 PIff arbitrary arbitrary
                    ,fmap PBexp arbitrary
                    ,liftM3 PAtom arbitrary arbitrary arbitrary
                    ,liftM2 PAll arbitrary arbitrary
                    ,return PTop
                    ]
  shrink = genericShrink

instance Arbitrary Expr where
  arbitrary = oneof [fmap ESym arbitrary
                    ,fmap ECon arbitrary
                    ,fmap EVar arbitrary
                    ,liftM2 ELit arbitrary arbitrary
                    ,liftM2 EApp arbitrary arbitrary
                    ,liftM3 EBin arbitrary arbitrary arbitrary
                    ,liftM3 EIte arbitrary arbitrary arbitrary
                    ,liftM2 ECst arbitrary arbitrary
                    ,return EBot
                    ]
  -- shrink = genericShrink

instance Arbitrary Brel where
  arbitrary = oneof (map return [Eq, Ne, Gt, Ge, Lt, Le, Ueq, Une])
  shrink = genericShrink

instance Arbitrary Bop where
  arbitrary = oneof (map return [Plus, Minus, Times, Div, Mod])
  shrink = genericShrink

instance Arbitrary SymConst where
  arbitrary = fmap SL arbitrary

instance Arbitrary Symbol where
  arbitrary = fmap (symbol :: Text -> Symbol) arbitrary

instance Arbitrary Text where
  arbitrary = fmap pack (arbitrary `suchThat` (not . null))

instance Arbitrary FTycon where
  arbitrary = fmap symbolFTycon arbitrary

instance Arbitrary Constant where
  arbitrary = oneof [fmap I arbitrary
                    ,fmap R arbitrary
                    ]
  shrink = genericShrink

instance Arbitrary a => Arbitrary (Located a) where
  arbitrary = fmap dummyLoc arbitrary
  shrink = fmap dummyLoc . shrink . val
