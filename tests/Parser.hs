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
  testGroup "ParserTests"
    [
      testSucceeds
    , testSpecP
    , testReservedAliases
    , testFails
    , testErrorReporting
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

    , testCase "local" $
       parseSingleSpec "local foo :: Nat -> Nat" @?=
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
          "Class (RClass {rcName = Sized, rcSupers = [], rcTyVars = [BTV \"s\"], rcMethods = [(\"size\" (dummyLoc),x:s a -> {v : Nat | v == sz x} (dummyLoc))]})"

    , testCase "import" $
       parseSingleSpec "import Foo" @?=
          "Impt \"Foo\""

    , testCase "data variance" $
       parseSingleSpec "data variance IO bivariant" @?=
          "Varia (\"IO\" (dummyLoc),[Bivariant])"

    , testCase "data" $
       parseSingleSpec "data Bob = B {foo :: Int}" @?=
          "DDecl DataDecl: data = \"Bob\", tyvars = [], sizeFun = Nothing, kind = DataUser"
    , testCase "newtype" $
       parseSingleSpec "newtype Foo = Bar {x :: Nat}" @?=
          "NTDecl DataDecl: data = \"Foo\", tyvars = [], sizeFun = Nothing, kind = DataUser"

    , testCase "include" $
       parseSingleSpec "include <listSet.hquals>" @?=
          "Incl \"listSet.hquals\""

    , testCase "invariant" $
       parseSingleSpec "invariant {v:Tree a | 0 <= ht v}" @?=
          "Invt {v : (Tree a) | 0 <= ht v} (dummyLoc)"

    , testCase "using" $
       parseSingleSpec "using (Tree a) as  {v:Tree a   | 0 <= height v}" @?=
          -- "IAlias ((Tree a) (dummyLoc),{v##0 : (Tree a) | 0 <= height v##0} (dummyLoc))"
             "IAlias ((Tree a) (dummyLoc),{v : (Tree a) | 0 <= height v} (dummyLoc))"

    , testCase "type" $
       parseSingleSpec "type PosInt = {v: Int | v >= 0}" @?=
          "Alias type PosInt   = {v : Int | v >= 0} -- defined at \"Fixpoint.Types.dummyLoc\" (line 0, column 0)"

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

    , testCase "decrease" $
       parseSingleSpec "decrease insert 3" @?=
          "Decr (\"insert\" (dummyLoc),[2])"

    , testCase "lazyvar" $
       parseSingleSpec "lazyvar z" @?=
          "LVars \"z\" (dummyLoc)"

    , testCase "lazy" $
       parseSingleSpec "lazy eval" @?=
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

-- Test that haskell functions having the same name as liquidhaskell keywords are parsed correctly
testReservedAliases :: TestTree
testReservedAliases =
  testGroup "reserved aliases"
    [ testCase "assume" $
       parseSingleSpec "assume :: Int -> Bool " @?=
          "Asrts ([\"assume\" (dummyLoc)],(lq_tmp$db##0:Int -> Bool (dummyLoc),Nothing))"

    , testCase "assert" $
       parseSingleSpec "assert :: Int -> Bool " @?=
          "Asrts ([\"assert\" (dummyLoc)],(lq_tmp$db##0:Int -> Bool (dummyLoc),Nothing))"

    , testCase "autosize" $
       parseSingleSpec "autosize :: Int -> Bool " @?=
          "Asrts ([\"autosize\" (dummyLoc)],(lq_tmp$db##0:Int -> Bool (dummyLoc),Nothing))"

    , testCase "axiomatize" $
       parseSingleSpec "axiomatize :: Int -> Bool " @?=
          "Asrts ([\"axiomatize\" (dummyLoc)],(lq_tmp$db##0:Int -> Bool (dummyLoc),Nothing))"

    , testCase "reflect" $
       parseSingleSpec "reflect :: Int -> Bool " @?=
          "Asrts ([\"reflect\" (dummyLoc)],(lq_tmp$db##0:Int -> Bool (dummyLoc),Nothing))"

    , testCase "measure" $
       parseSingleSpec "measure :: Int -> Bool " @?=
          "Asrts ([\"measure\" (dummyLoc)],(lq_tmp$db##0:Int -> Bool (dummyLoc),Nothing))"


    , testCase "define 1" $
       parseSingleSpec "define :: Int -> Bool " @?=
          "Asrts ([\"define\" (dummyLoc)],(lq_tmp$db##0:Int -> Bool (dummyLoc),Nothing))"

    , testCase "define 2" $
       parseSingleSpec "define GHC.Types.True = (true)" @?=
          "Define (\"GHC.Types.True\" (dummyLoc),\"(true)\")"

    , testCase "defined" $
       parseSingleSpec "defined :: Int -> Bool " @?=
          "Asrts ([\"defined\" (dummyLoc)],(lq_tmp$db##0:Int -> Bool (dummyLoc),Nothing))"

    , testCase "inline" $
       parseSingleSpec "inline :: Int -> Bool " @?=
          "Asrts ([\"inline\" (dummyLoc)],(lq_tmp$db##0:Int -> Bool (dummyLoc),Nothing))"

    , testCase "bound" $
       parseSingleSpec "bound :: Int -> Bool " @?=
          "Asrts ([\"bound\" (dummyLoc)],(lq_tmp$db##0:Int -> Bool (dummyLoc),Nothing))"

    , testCase "invariant" $
       parseSingleSpec "invariant :: Int -> Bool " @?=
          "Asrts ([\"invariant\" (dummyLoc)],(lq_tmp$db##0:Int -> Bool (dummyLoc),Nothing))"

    , testCase "predicate" $
       parseSingleSpec "predicate :: Int -> Bool " @?=
          "Asrts ([\"predicate\" (dummyLoc)],(lq_tmp$db##0:Int -> Bool (dummyLoc),Nothing))"

    , testCase "expression" $
       parseSingleSpec "expression :: Int -> Bool " @?=
          "Asrts ([\"expression\" (dummyLoc)],(lq_tmp$db##0:Int -> Bool (dummyLoc),Nothing))"

    , testCase "embed" $
       parseSingleSpec "embed :: Int -> Bool " @?=
          "Asrts ([\"embed\" (dummyLoc)],(lq_tmp$db##0:Int -> Bool (dummyLoc),Nothing))"

    , testCase "qualif" $
       parseSingleSpec "qualif :: Int -> Bool " @?=
          "Asrts ([\"qualif\" (dummyLoc)],(lq_tmp$db##0:Int -> Bool (dummyLoc),Nothing))"
    ]

-- ---------------------------------------------------------------------

testSucceeds :: TestTree
testSucceeds =
  testGroup "Should succeed"
    [ testCase "x :: Int" $
       (parseSingleSpec "x :: Int") @?=
          "Asrts ([\"x\" (dummyLoc)],(Int (dummyLoc),Nothing))"

    , testCase "x :: a" $
       (parseSingleSpec "x :: a") @?=
          "Asrts ([\"x\" (dummyLoc)],(a (dummyLoc),Nothing))"

    , testCase "x :: a -> a" $
       (parseSingleSpec "x :: a -> a") @?=
          -- "Asrts ([\"x\" (dummyLoc)],(a -> a (dummyLoc),Nothing))"
             "Asrts ([\"x\" (dummyLoc)],(lq_tmp$db##0:a -> a (dummyLoc),Nothing))"

    , testCase "x :: Int -> Int" $
       (parseSingleSpec "x :: Int -> Int") @?=
          -- "Asrts ([\"x\" (dummyLoc)],(Int -> Int (dummyLoc),Nothing))"
             "Asrts ([\"x\" (dummyLoc)],(lq_tmp$db##0:Int -> Int (dummyLoc),Nothing))"

    , testCase "k:Int -> Int" $
       (parseSingleSpec "x :: k:Int -> Int") @?=
          "Asrts ([\"x\" (dummyLoc)],(k:Int -> Int (dummyLoc),Nothing))"

    , testCase "type spec 1 " $
       parseSingleSpec "type IncrListD a D = [a]<{\\x y -> (x+D) <= y}>" @?=
          "Alias type IncrListD \"a\" \"D\" = [a] -- defined at \"Fixpoint.Types.dummyLoc\" (line 0, column 0)"

    , testCase "type spec 2 " $
       parseSingleSpec "takeL :: Ord a => x:a -> [a] -> [{v:a|v<=x}]" @?=
          -- "Asrts ([\"takeL\" (dummyLoc)],((Ord a) -> x:a -> lq_tmp$db##1:[a] -> [{v##2 : a | v##2 <= x}] (dummyLoc),Nothing))"
             "Asrts ([\"takeL\" (dummyLoc)],((Ord a) -> x:a -> lq_tmp$db##1:[a] -> [{v : a | v <= x}] (dummyLoc),Nothing))"

    , testCase "type spec 3" $
       parseSingleSpec "bar :: t 'Nothing" @?=
          "Asrts ([\"bar\" (dummyLoc)],(t Nothing (dummyLoc),Nothing))"

    , testCase "type spec 4" $
       parseSingleSpec "Cons :: forall <l>.a -> L^l a -> L^l a" @?=
          "Asrts ([\"Cons\" (dummyLoc)],(lq_tmp$db##0:a -> lq_tmp$db##1:(L a) -> (L a) (dummyLoc),Nothing))"

    , testCase "type spec 5" $
       parseSingleSpec "mapKeysWith :: (Ord k2) => (a -> a -> a) -> (k1->k2) -> OMap k1 a -> OMap k2 a" @?=
             "Asrts ([\"mapKeysWith\" (dummyLoc)],((Ord k2) -> lq_tmp$db##2:(lq_tmp$db##3:a -> lq_tmp$db##4:a -> a) -> lq_tmp$db##6:(lq_tmp$db##7:k1 -> k2) -> lq_tmp$db##9:(OMap k1 a) -> (OMap k2 a) (dummyLoc),Nothing))"

    , testCase "type spec 6 " $
       parseSingleSpec (unlines $
         [ "data Tree [ht] a = Nil"
         , "            | Tree { key :: a"
         , "                   , l   :: Tree {v:a | v < key }"
         , "                   , r   :: Tree {v:a | key < v }"
         , "                   }" ])
        @?=
          "DDecl DataDecl: data = \"Tree\", tyvars = [\"a\"], sizeFun = Just SymSizeFun \"ht\", kind = DataUser"

    , testCase "type spec 7" $
       parseSingleSpec "type AVLL a X    = AVLTree {v:a | v < X}" @?=
              "Alias type AVLL \"a\" \"X\" = (AVLTree {v : a | v < X}) -- defined at \"Fixpoint.Types.dummyLoc\" (line 0, column 0)"

    , testCase "type spec 8" $
       parseSingleSpec "type AVLR a X    = AVLTree {v:a |X< v} " @?=
             "Alias type AVLR \"a\" \"X\" = (AVLTree {v : a | X < v}) -- defined at \"Fixpoint.Types.dummyLoc\" (line 0, column 0)"

    , testCase "type spec 9 " $
       parseSingleSpec (unlines $
      [ "assume (++) :: forall <p :: a -> Bool, q :: a -> Bool, r :: a -> Bool>."
      , "  {x::a<p> |- a<q> <: {v:a| x <= v}} "
      , "  {a<p> <: a<r>} "
      , "  {a<q> <: a<r>} "
      , "  Ord a => OList (a<p>) -> OList (a<q>) -> OList a<r> "])
        @?=
             "Assm (\"(++)\" (dummyLoc),(Ord a) =>\n{x :: {VV : a | true} |- {VV : a | true} <: {v : a | x <= v}} =>\n{|- {VV : a | true} <: {VV : a | true}} =>\n{|- {VV : a | true} <: {VV : a | true}} =>\nlq_tmp$db##13:(OList {VV : a | true}) -> lq_tmp$db##15:(OList {VV : a | true}) -> (OList {VV : a | true}) (dummyLoc))"

    , testCase "type spec 10" $
       parseSingleSpec (unlines $
          [ "data AstF f <ix :: AstIndex -> Bool>"
          , "  = Lit Int    (i :: AstIndex<ix>)"
          , "  | Var String (i :: AstIndex<ix>)"
          , "  | App (fn :: f) (arg :: f)"
          , "  | Paren (ast :: f)" ])
          @?=
          "DDecl DataDecl: data = \"AstF\", tyvars = [\"f\"], sizeFun = Nothing, kind = DataUser"

    , testCase "type spec 11" $
       parseSingleSpec "assume     :: b:_ -> a -> {v:a | b} " @?=
          "Asrts ([\"assume\" (dummyLoc)],(b:{VV : _ | $HOLE} -> lq_tmp$db##0:a -> {v : a | b} (dummyLoc),Nothing))"

    , testCase "type spec 12" $
       parseSingleSpec (unlines $
          [ "app :: forall <p :: Int -> Bool, q :: Int -> Bool>. "
          , "       {Int<q> <: Int<p>}"
          , "       {x::Int<q> |- {v:Int| v = x + 1} <: Int<q>}"
          , "       (Int<p> -> ()) -> x:Int<q> -> ()" ])
          @?=
             "Asrts ([\"app\" (dummyLoc)],({|- Int <: Int} =>\n{x :: Int |- {v : Int | v == x + 1} <: Int} =>\nlq_tmp$db##8:(lq_tmp$db##9:Int -> ()) -> x:Int -> () (dummyLoc),Nothing))"

    , testCase "type spec 13" $
       parseSingleSpec (unlines $
          [ " ssum :: forall<p :: a -> Bool, q :: a -> Bool>. "
          , "         {{v:a | v == 0} <: a<q>}"
          , "         {x::a<p> |- {v:a | x <= v} <: a<q>}"
          , "         xs:[{v:a<p> | 0 <= v}] -> {v:a<q> | len xs >= 0 && 0 <= v } "])
          @?=
             "Asrts ([\"ssum\" (dummyLoc)],({|- {v : a | v == 0} <: {VV : a | true}} =>\n{x :: {VV : a | true} |- {v : a | x <= v} <: {VV : a | true}} =>\nxs:[{v : a | 0 <= v}] -> {v : a | len xs >= 0\n                                  && 0 <= v} (dummyLoc),Nothing))"

    , testCase "type spec 14" $
       parseSingleSpec (unlines $
          [ " predicate ValidChunk V XS N "
          , " = if len XS == 0 "
          , "     then (len V == 0) "
          , "     else (((1 < len XS && 1 < N) => (len V  < len XS)) "
          , "       && ((len XS <= N ) => len V == 1)) "])
          @?=
          "EAlias type ValidChunk  \"V\" \"XS\" \"N\" = PAnd [PImp (PAtom Eq (EApp (EVar \"len\") (EVar \"XS\")) (ECon (I 0))) (PAtom Eq (EApp (EVar \"len\") (EVar \"V\")) (ECon (I 0))),PImp (PNot (PAtom Eq (EApp (EVar \"len\") (EVar \"XS\")) (ECon (I 0)))) (PAnd [PImp (PAnd [PAtom Lt (ECon (I 1)) (EApp (EVar \"len\") (EVar \"XS\")),PAtom Lt (ECon (I 1)) (EVar \"N\")]) (PAtom Lt (EApp (EVar \"len\") (EVar \"V\")) (EApp (EVar \"len\") (EVar \"XS\"))),PImp (PAtom Le (EApp (EVar \"len\") (EVar \"XS\")) (EVar \"N\")) (PAtom Eq (EApp (EVar \"len\") (EVar \"V\")) (ECon (I 1)))])] -- defined at \"Fixpoint.Types.dummyLoc\" (line 0, column 0)"

    , testCase "type spec 15" $
       parseSingleSpec "assume (=*=.) :: Arg a => f:(a -> b) -> g:(a -> b) -> (r:a -> {f r == g r}) -> {v:(a -> b) | f == g}" @?=
             "Assm (\"(=*=.)\" (dummyLoc),(Arg a) -> f:(lq_tmp$db##1:a -> b) -> g:(lq_tmp$db##3:a -> b) -> lq_tmp$db##5:(r:a -> {VV : _ | f r == g r}) -> {VV : lq_tmp$db##6:a -> b | f == g} (dummyLoc))"

    , testCase "type spec 16" $
       parseSingleSpec "sort :: (Ord a) => xs:[a] -> OListN a {len xs}" @?=
           "Asrts ([\"sort\" (dummyLoc)],((Ord a) -> xs:[a] -> (OListN a {len xs}) (dummyLoc),Nothing))"

    , testCase "type spec 17" $
       parseSingleSpec " ==. :: x:a -> y:{a| x == y} -> {v:b | v ~~ x && v ~~ y } " @?=
           "Asrts ([\"==.\" (dummyLoc)],(x:a -> y:{y : a | x == y} -> {v : b | v ~~ x\n                                      && v ~~ y} (dummyLoc),Nothing))"

    , testCase "type spec 18" $
       parseSingleSpec "measure snd :: (a,b) -> b" @?=
           "Meas snd :: lq_tmp$db##0:(a, b) -> b"

    , testCase "type spec 19" $
       parseSingleSpec "returnST :: xState:a \n             -> ST <{\\xs xa v -> (xa = xState)}> a s " @?=
                     -- returnST :: a -> ST a s
                     -- returnST x = S $ \s -> (x, s)
           "Asrts ([\"returnST\" (dummyLoc)],(xState:a -> (ST a s) (dummyLoc),Nothing))"

    , testCase "type spec 20" $
       parseSingleSpec "makeq :: l:_ -> r:{ _ | size r <= size l + 1} -> _ " @?=
           "Asrts ([\"makeq\" (dummyLoc)],(l:{VV : _ | $HOLE} -> r:{r : _ | size r <= size l + 1} -> {VV : _ | $HOLE} (dummyLoc),Nothing))"

    , testCase "type spec 21" $
       parseSingleSpec "newRGRef :: forall <p :: a -> Bool, r :: a -> a -> Bool >.\n   e:a<p> ->\n  e2:a<r e> ->\n  f:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->\n IO (RGRef <p, r> a)" @?=
            "Asrts ([\"newRGRef\" (dummyLoc)],(e:{VV : a | true} -> e2:{VV : a | true} -> f:(x:{VV : a | true} -> y:{VV : a | true} -> {v : a | v == y}) -> (IO (RGRef a)) (dummyLoc),Nothing))"

    , testCase "type spec 22" $
       parseSingleSpec "cycle        :: {v: [a] | len(v) > 0 } -> [a]" @?=
            "Asrts ([\"cycle\" (dummyLoc)],(v:{v : [a] | len v > 0} -> [a] (dummyLoc),Nothing))"

    , testCase "type spec 23" $
       parseSingleSpec "cons :: x:a -> _ -> {v:[a] | hd v = x} " @?=
         "Asrts ([\"cons\" (dummyLoc)],(x:a -> lq_tmp$db##0:{VV : _ | $HOLE} -> {v : [a] | hd v == x} (dummyLoc),Nothing))"

    , testCase "type spec 24" $
       parseSingleSpec "set :: a:Vector a -> i:Idx a -> a -> {v:Vector a | vlen v = vlen a}" @?=
         "Asrts ([\"set\" (dummyLoc)],(a:(Vector a) -> i:(Idx a) -> lq_tmp$db##0:a -> {v : (Vector a) | vlen v == vlen a} (dummyLoc),Nothing))"

    , testCase "type spec 25" $
       parseSingleSpec "assume GHC.Prim.+#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v: GHC.Prim.Int# | v = x + y}" @?=
         "Assm (\"GHC.Prim.+#\" (dummyLoc),x:Int# -> y:Int# -> {v : Int# | v == x + y} (dummyLoc))"

    , testCase "type spec 26" $
       parseSingleSpec " measure isEVar " @?=
         "HMeas \"isEVar\" (dummyLoc)"

    , testCase "type spec 27" $
       parseSingleSpec (unlines $
         [ "data List a where"
         , "    Nil  :: List a "
         , "  | Cons :: listHead:a -> listTail:List a -> List a  "])
        @?=
          "DDecl DataDecl: data = \"List\", tyvars = [\"a\"], sizeFun = Nothing, kind = DataUser"

    , testCase "type spec 28" $
       parseSingleSpec (unlines $
         [ "data List2 a b <p :: a -> Bool> where"
         , "    Nil2  :: List2 a "
         , "  | Cons2 :: listHead:a -> listTail:List a -> List2 a b"])
        @?=
          "DDecl DataDecl: data = \"List2\", tyvars = [\"a\",\"b\"], sizeFun = Nothing, kind = DataUser"

    , testCase "type spec 29" $
       parseSingleSpec (unlines $
         [ "data Ev :: Peano -> Prop where"
         , "  EZ  :: Prop (Ev Z)"
         , "| ESS :: n:Peano -> Prop (Ev n) -> Prop (Ev (S (S n)))"
         ])
        @?=
          "DDecl DataDecl: data = \"Ev\", tyvars = [], sizeFun = Nothing, kind = DataUser"

    , testCase "type spec 30" $
       parseSingleSpec (unlines $
         [ "measure fst :: (a,b) -> a"
         , "fst (a,b) = a"
         ])
        @?=
          "Meas fst :: lq_tmp$db##0:(a, b) -> a\nfst [] ((,)a b) = a"
    ]

-- ---------------------------------------------------------------------

testFails :: TestTree
testFails =
  testGroup "Does fail"
    [ testCase "Maybe k:Int -> Int" $
          parseSingleSpec "x :: Maybe k:Int -> Int" @?=
            "<test>:1:13: Error: Cannot parse specification:\n    unexpected ':'\n    expecting stratumP, monoPredicateP, white space, bareTyArgP, mmonoPredicateP, \"->\", \"=>\", \"/\" or end of input"
    ]


-- ---------------------------------------------------------------------

testErrorReporting :: TestTree
testErrorReporting =
  testGroup "Error reporting"
    [ testCase "assume mallocForeignPtrBytes :: n:Nat -> IO (ForeignPtrN a n " $
          parseSingleSpec "assume mallocForeignPtrBytes :: n:Nat -> IO (ForeignPtrN a n " @?=
            "<test>:1:62: Error: Cannot parse specification:\n    unexpected end of input\n    expecting bareTyArgP"

    , testCase "Missing |" $
          parseSingleSpec "ff :: {v:Nat  v >= 0 }" @?=
          -- parseSingleSpec "ff :: {v :  }" @?=
            "<test>:1:9: Error: Cannot parse specification:\n    unexpected \":\"\n    expecting operator, white space or \"}\""
    ]

-- ---------------------------------------------------------------------

-- | Parse a single type signature containing LH refinements. To be
-- used in the REPL.
parseSingleSpec :: String -> String
parseSingleSpec src =
  case LH.singleSpecP (initialPos "<test>") src of
    Left err  -> show err
    Right res -> show $ dummyLocs res

gadtSpec :: String
gadtSpec = unlines
  [ "data Ev where"
  , "   EZ  :: {v:Ev | prop v = Ev Z}"
  , " | ESS :: n:Peano -> {v:Ev | prop v = Ev n} -> {v:Ev | prop v = Ev (S (S n)) }"
  ]

------------------------------------------------------------------------

dummyLocs :: (Data a) => a -> a
dummyLocs = everywhere (mkT posToDummy)
  where
    posToDummy :: SourcePos -> SourcePos
    posToDummy _ = dummyPos "Fixpoint.Types.dummyLoc"

-- ---------------------------------------------------------------------
