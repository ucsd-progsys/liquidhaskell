{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TemplateHaskell #-}

import           Control.Monad (forM, when)
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Runners.AntXML

import Language.Haskell.Liquid.WiredIn (derivingClasses)

import qualified GHC.Classes
import qualified GHC.Internal.Base
import qualified GHC.Internal.Data.Foldable
import qualified GHC.Internal.Data.Traversable
import qualified GHC.Internal.Enum
import qualified GHC.Internal.Read
import qualified GHC.Internal.Real
import qualified GHC.Internal.Show

main :: IO ()
main =
  defaultMainWithIngredients (antXMLRunner:defaultIngredients) testTree

testTree :: TestTree
testTree =
    testGroup "WiredIn names"
      [ testCase "derivingClasses" testDerivingClasses
      ]

testDerivingClasses :: IO ()
testDerivingClasses = do
    let xs = $((TH.lift . concat =<<) $ forM derivingClasses $ \s -> do
               mName <- TH.lookupTypeName s
               case mName of
                 Nothing ->
                   pure [s ++ " is not in scope"]
                 Just n ->
                   case TH.nameModule n of
                     Nothing ->
                       pure [s ++ " doesn't have a module qualifier"]
                     Just m
                       | actual == s ->
                         pure []
                       | otherwise ->
                         pure [s ++ " is defined at another place: " ++ actual]
                       where
                         actual = m ++ "." ++ TH.nameBase n
             ) :: [String]
    when (not $ null xs) $
      assertFailure $ unlines xs

