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

    , testCase "type spec 3" $
       parseSingleSpec "bar :: t 'Nothing" @?=
          "Asrts ([\"bar\" (dummyLoc)],(t Nothing (dummyLoc),Nothing))"

    , testCase "type spec 4" $
       parseSingleSpec "Cons :: forall <l>.a -> L^l a -> L^l a" @?=
          "Asrts ([\"Cons\" (dummyLoc)],(lq_tmp$db##0:a -> lq_tmp$db##1:(L a) -> (L a) (dummyLoc),Nothing))"

    , testCase "type spec 5" $
       parseSingleSpec "mapKeysWith :: (Ord k2) => (a -> a -> a) -> (k1->k2) -> OMap k1 a -> OMap k2 a" @?=
          "Asrts ([\"mapKeysWith\" (dummyLoc)],((Ord k2) -> lq_tmp$db##1:(lq_tmp$db##2:a -> lq_tmp$db##3:a -> a) -> lq_tmp$db##4:(lq_tmp$db##5:k1 -> k2) -> lq_tmp$db##6:(OMap k1 a) -> (OMap k2 a) (dummyLoc),Nothing))"

    , testCase "type spec 6" $
       parseSingleSpec (unlines $
         [ "data Tree [ht] a = Nil"
         , "            | Tree { key :: a"
         , "                   , l   :: Tree {v:a | v < key }"
         , "                   , r   :: Tree {v:a | key < v }"
         , "                   }" ])
        @?=
          "DDecl DataDecl: data = \"Tree\" (dummyLoc), tyvars = [\"a\"]"

    , testCase "type spec 7" $
       -- parseSingleSpec "type AVLL a X    = AVLTree {v:a | v < X}" @?=
       parseSingleSpec "type AVLL a X    = AVLTree {v:a | v < X}" @?=
          "Alias type AVLL \"a\" \"X\" = (AVLTree {v##0 : a | v##0 < X}) -- defined at \"Fixpoint.Types.dummyLoc\" (line 0, column 0)"

    , testCase "type spec 8" $
       parseSingleSpec "type AVLR a X    = AVLTree {v:a |X< v} " @?=
          "Alias type AVLR \"a\" \"X\" = (AVLTree {v##0 : a | X < v##0}) -- defined at \"Fixpoint.Types.dummyLoc\" (line 0, column 0)"

    , testCase "type spec 9" $
       parseSingleSpec (unlines $
      [ "assume (++) :: forall <p :: a -> Bool, q :: a -> Bool, r :: a -> Bool>."
      , "  {x::a<p> |- a<q> <: {v:a| x <= v}} "
      , "  {a<p> <: a<r>} "
      , "  {a<q> <: a<r>} "
      , "  Ord a => OList (a<p>) -> OList (a<q>) -> OList a<r> "])
        @?=
          "Assm (\"(++)\" (dummyLoc),(Ord a) =>\n{x :: {VV : a | true} |- {VV : a | true} <: {v##3 : a | x <= v##3}} =>\n{|- {VV : a | true} <: {VV : a | true}} =>\n{|- {VV : a | true} <: {VV : a | true}} =>\nlq_tmp$db##5:(OList {VV : a | true}) -> lq_tmp$db##6:(OList {VV : a | true}) -> (OList {VV : a | true}) (dummyLoc))"

    , testCase "type spec 10" $
       parseSingleSpec (unlines $
          [ "data AstF f <ix :: AstIndex -> Bool>"
          , "  = Lit Int    (i :: AstIndex<ix>)"
          , "  | Var String (i :: AstIndex<ix>)"
          , "  | App (fn :: f) (arg :: f)"
          , "  | Paren (ast :: f)" ])
          @?=
          "DDecl DataDecl: data = \"AstF\" (dummyLoc), tyvars = [\"f\"]"

    , testCase "type spec 11" $
       parseSingleSpec "assume     :: b:_ -> a -> {v:a | b} " @?=
          "Asrts ([\"assume\" (dummyLoc)],(b:{VV : _ | $HOLE} -> lq_tmp$db##0:a -> {v##1 : a | b} (dummyLoc),Nothing))"

    , testCase "type spec 12" $
       parseSingleSpec (unlines $
          [ "app :: forall <p :: Int -> Bool, q :: Int -> Bool>. "
          , "       {Int<q> <: Int<p>}"
          , "       {x::Int<q> |- {v:Int| v = x + 1} <: Int<q>}"
          , "       (Int<p> -> ()) -> x:Int<q> -> ()" ])
          @?=
          "Asrts ([\"app\" (dummyLoc)],({|- Int <: Int} =>\n{x :: Int |- {v##2 : Int | v##2 == x + 1} <: Int} =>\nlq_tmp$db##3:(lq_tmp$db##4:Int -> ()) -> x:Int -> () (dummyLoc),Nothing))"

    , testCase "type spec 13" $
       parseSingleSpec (unlines $
          [ " ssum :: forall<p :: a -> Bool, q :: a -> Bool>. "
          , "         {{v:a | v == 0} <: a<q>}"
          , "         {x::a<p> |- {v:a | x <= v} <: a<q>}"
          , "         xs:[{v:a<p> | 0 <= v}] -> {v:a<q> | len xs >= 0 && 0 <= v } "])
          @?=
          "Asrts ([\"ssum\" (dummyLoc)],({|- {v##2 : a | v##2 == 0} <: {VV : a | true}} =>\n{x :: {VV : a | true} |- {v##3 : a | x <= v##3} <: {VV : a | true}} =>\nxs:[{v##4 : a | 0 <= v##4}] -> {v##5 : a | len xs >= 0\n                                           && 0 <= v##5} (dummyLoc),Nothing))"
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
