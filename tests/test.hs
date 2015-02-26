{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Main where

import Language.Fixpoint.Names
import Language.Fixpoint.Parse
import Language.Fixpoint.PrettyPrint
import Language.Fixpoint.Types

import Control.Monad
import Data.Proxy
import Data.Text (Text, cons, inits, pack)
import Test.QuickCheck
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
