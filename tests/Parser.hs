{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DoAndIfThenElse     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Simple test suite to test the parser.
--
-- Run as:
--
-- $ stack test :liquidhaskell-parser

module Main where

import           Data.Data
import           Data.Generics.Aliases
import           Data.Generics.Schemes
import           Language.Fixpoint.Types.Spans
import qualified Language.Haskell.Liquid.Parse as LH
-- import qualified Language.Haskell.Liquid.Types as LH
import           Text.Parsec.Pos
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Runners.AntXML

-- ---------------------------------------------------------------------

-- | Test suite entry point, returns exit failure if any test fails.
main :: IO ()
main =  defaultMainWithIngredients (
                antXMLRunner:defaultIngredients
              ) tests

tests :: TestTree
tests =
  testGroup "Tests"
    [
      testSucceeds
    , testFails
    , testSpecP
    ]

-- ---------------------------------------------------------------------

-- Test that the top level production works, each of the sub-elements will be tested separately
testSpecP :: TestTree
testSpecP =
  testGroup "specP"
    [ testCase "assume" $
       parseSingleSpec "assume foo :: a -> a " @?=
          "Assm (\"foo\" (dummyLoc),lq_tmp$db##0:a -> a (dummyLoc))"

    , testCase "assert" $
       parseSingleSpec "assert myabs :: Int -> PosInt" @?=
          "Asrt (\"myabs\" (dummyLoc),lq_tmp$db##0:Int -> PosInt (dummyLoc))"

    , testCase "autosize" $
       parseSingleSpec "autosize List" @?=
          "ASize \"List\" (dummyLoc)"

    , testCase "Local" $
       parseSingleSpec "Local foo :: Nat -> Nat" @?=
          "LAsrt (\"foo\" (dummyLoc),lq_tmp$db##0:Nat -> Nat (dummyLoc))"

    , testCase "axiomatize" $
       parseSingleSpec "axiomatize fibA" @?=
          "Reflect \"fibA\" (dummyLoc)"

    , testCase "reflect" $
       parseSingleSpec "reflect map" @?=
          "Reflect \"map\" (dummyLoc)"

    , testCase "measure HMeas" $
       parseSingleSpec "measure isAbs" @?=
          "HMeas \"isAbs\" (dummyLoc)"

    , testCase "measure Meas" $
       parseSingleSpec "measure fv :: Expr -> (Set Bndr)" @?=
          "Meas fv :: lq_tmp$db##0:Expr -> (Set Bndr)"

    , testCase "define" $
       parseSingleSpec "define $ceq = eqN" @?=
          "Define (\"$ceq\" (dummyLoc),\"eqN\")"

    , testCase "infixl" $
       parseSingleSpec "infixl 9 +++" @?=
          "BFix ()"

    , testCase "infixr" $
       parseSingleSpec "infixr 9 +++" @?=
          "BFix ()"

    , testCase "infix" $
       parseSingleSpec "infix 9 +++" @?=
          "BFix ()"

    , testCase "defined" $ -- TODO:AZ synonym for "measure"?
       parseSingleSpec "defined fv :: Expr -> (Set Bndr)" @?=
          "Meas fv :: lq_tmp$db##0:Expr -> (Set Bndr)"

    , testCase "inline" $
       parseSingleSpec "inline eqelems" @?=
          "Inline \"eqelems\" (dummyLoc)"

    , testCase "bound PBound" $
       parseSingleSpec "bound Foo = true" @?=
          "PBound bound Foo forall [] . [] =  true"

    , testCase "bound HBound" $
       parseSingleSpec "bound step" @?=
          "HBound \"step\" (dummyLoc)"

    , testCase "class measure" $
       parseSingleSpec "class measure sz :: forall a. a -> Int" @?=
          "CMeas sz :: lq_tmp$db##0:a -> Int"

    , testCase "instance measure" $
       parseSingleSpec "instance measure sz :: MList a -> Int" @?=
          "IMeas sz :: lq_tmp$db##0:(MList a) -> Int"

    , testCase "instance" $
       parseSingleSpec "instance VerifiedNum Int where\n  - :: x:Int -> y:Int -> OkInt {x - y} " @?=
          "RInst (RI {riclass = VerifiedNum, ritype = [Int (dummyLoc)], risigs = [(\"-\" (dummyLoc),RISig x:Int -> y:Int -> (OkInt {x - y}) (dummyLoc))]})"

    , testCase "class" $
       parseSingleSpec "class Sized s where\n  size :: forall a. x:s a -> {v:Nat | v = sz x}" @?=
          "Class (RClass {rcName = Sized, rcSupers = [], rcTyVars = [BTV \"s\"], rcMethods = [(\"size\" (dummyLoc),x:s a -> {v##0 : Nat | v##0 == sz x} (dummyLoc))]})"

    , testCase "import" $
       parseSingleSpec "import Foo" @?=
          "Impt \"Foo\""

    , testCase "data variance" $
       parseSingleSpec "data variance IO bivariant" @?=
          "Varia (\"IO\" (dummyLoc),[Bivariant])"

    , testCase "data" $
       parseSingleSpec "data Bob = B {foo :: Int}" @?=
          "DDecl DataDecl: data = \"Bob\" (dummyLoc), tyvars = []"

    , testCase "newtype" $
       parseSingleSpec "newtype Foo = Bar {x :: Nat}" @?=
          "NTDecl DataDecl: data = \"Foo\" (dummyLoc), tyvars = []"

    , testCase "include" $
       parseSingleSpec "include <listSet.hquals>" @?=
          "Incl \"listSet.hquals\""

    , testCase "invariant" $
       parseSingleSpec "invariant {v:Tree a | 0 <= ht v}" @?=
          "Invt {v##0 : (Tree a) | 0 <= ht v##0} (dummyLoc)"

    , testCase "using" $
       parseSingleSpec "using (Tree a) as  {v:Tree a   | 0 <= height v}" @?=
          "IAlias ((Tree a) (dummyLoc),{v##0 : (Tree a) | 0 <= height v##0} (dummyLoc))"

    , testCase "type" $
       parseSingleSpec "type PosInt = {v: Int | v >= 0}" @?=
          "Alias type PosInt   = {v##0 : Int | v##0 >= 0} -- defined at \"Fixpoint.Types.dummyLoc\" (line 0, column 0)"

    , testCase "predicate" $
       parseSingleSpec "predicate Pos X  = X > 0" @?=
          "EAlias type Pos  \"X\" = PAtom Gt (EVar \"X\") (ECon (I 0)) -- defined at \"Fixpoint.Types.dummyLoc\" (line 0, column 0)"

    , testCase "expression" $
       parseSingleSpec "expression Avg Xs = ((sumD Xs) / (lenD Xs))" @?=
          "EAlias type Avg  \"Xs\" = EBin Div (EApp (EVar \"sumD\") (EVar \"Xs\")) (EApp (EVar \"lenD\") (EVar \"Xs\")) -- defined at \"Fixpoint.Types.dummyLoc\" (line 0, column 0)"

    , testCase "embed" $
       parseSingleSpec "embed Set as Set_Set" @?=
          "Embed (\"Set\" (dummyLoc),TC \"Set_Set\" (dummyLoc) (TCInfo {tc_isNum = False, tc_isReal = False, tc_isString = False}))"

    , testCase "qualif" $
       parseSingleSpec "qualif Foo(v:Int): v < 0" @?=
          "Qualif (Q {qName = \"Foo\", qParams = [(\"v\",FInt)], qBody = PAtom Lt (EVar \"v\") (ECon (I 0)), qPos = \"Fixpoint.Types.dummyLoc\" (line 0, column 0)})"

    , testCase "Decrease" $
       parseSingleSpec "Decrease insert 3" @?=
          "Decr (\"insert\" (dummyLoc),[2])"

    , testCase "LAZYVAR" $
       parseSingleSpec "LAZYVAR z" @?=
          "LVars \"z\" (dummyLoc)"

    , testCase "Strict" $
       parseSingleSpec "Strict eval" @?=
          "Lazy \"eval\" (dummyLoc)"

    , testCase "Lazy" $
       parseSingleSpec "Lazy eval" @?=
          "Lazy \"eval\" (dummyLoc)"

    , testCase "automatic-instances" $
       parseSingleSpec "automatic-instances foo with 5" @?=
          "Insts (\"foo\" (dummyLoc),Just 5)"

    , testCase "LIQUID" $
       parseSingleSpec "LIQUID \"--automatic-instances=liquidinstances\" " @?=
          "Pragma \"--automatic-instances=liquidinstances\" (dummyLoc)"

    , testCase "default parser (Asrts)" $
       parseSingleSpec " assumeIndices :: t:ByteStringNE -> s:BS.ByteString -> [OkPos t s]" @?=
          "Asrts ([\"assumeIndices\" (dummyLoc)],(t:ByteStringNE -> s:ByteString -> [(OkPos t s)] (dummyLoc),Nothing))"
    ]

-- ---------------------------------------------------------------------

testSucceeds :: TestTree
testSucceeds =
  testGroup "Should succeed"
    [ testCase "Int" $
       (parseSingleSpec "x :: Int") @?=
          "Asrts ([\"x\" (dummyLoc)],(Int (dummyLoc),Nothing))"

    , testCase "k:Int -> Int" $
       (parseSingleSpec "x :: k:Int -> Int") @?=
          "Asrts ([\"x\" (dummyLoc)],(k:Int -> Int (dummyLoc),Nothing))"

    , testCase "type spec 1" $
       parseSingleSpec "type IncrListD a D = [a]<{\\x y -> (x+D) <= y}>" @?=
          "Alias type IncrListD \"a\" \"D\" = [a] -- defined at \"Fixpoint.Types.dummyLoc\" (line 0, column 0)"

    , testCase "type spec 2" $
       parseSingleSpec "takeL :: Ord a => x:a -> [a] -> [{v:a|v<=x}]" @?=
          "Asrts ([\"takeL\" (dummyLoc)],((Ord a) -> x:a -> lq_tmp$db##1:[a] -> [{v##2 : a | v##2 <= x}] (dummyLoc),Nothing))"

    ]

-- ---------------------------------------------------------------------

testFails :: TestTree
testFails =
  testGroup "Does fail"
    [ testCase "Maybe k:Int -> Int" $
          parseSingleSpec "x :: Maybe k:Int -> Int" @?=
            "<test>:1:13: Error: Cannot parse specification:\n    Leftover while parsing"
    ]

-- ---------------------------------------------------------------------

-- | Parse a single type signature containing LH refinements. To be
-- used in the REPL.
parseSingleSpec :: String -> String
parseSingleSpec src =
  case LH.singleSpecP (initialPos "<test>") src of
    Left err  -> show err
    Right res -> show $ dummyLocs res

-- ---------------------------------------------------------------------

dummyLocs :: (Data a) => a -> a
dummyLocs = everywhere (mkT posToDummy)
  where
    posToDummy :: SourcePos -> SourcePos
    posToDummy _ = dummyPos "Fixpoint.Types.dummyLoc"
