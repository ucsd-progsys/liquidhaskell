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
import           Data.Char (isSpace) 
import           Data.Generics.Aliases
import           Data.Generics.Schemes

import           Language.Fixpoint.Types.Spans
import qualified Language.Haskell.Liquid.Parse as LH
import qualified Language.Fixpoint.Types       as F 

import           Text.Parsec.Pos
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Runners.AntXML

-- ---------------------------------------------------------------------

-- | Test suite entry point, returns exit failure if any test fails.
main :: IO ()
-- main = do 
--   print $ parseSingleSpec "type IncrListD a D = [a]<{\\x y -> (x+D) <= y}>"
--   return ()
main =  defaultMainWithIngredients (
                antXMLRunner:defaultIngredients
              ) tests

tests :: TestTree
tests =
  testGroup "ParserTests"
    [ testSucceeds
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
       parseSingleSpec "assume foo :: a -> a " @?==
          "assume foo :: lq_tmp$db##0:a -> a"

    , testCase "assert" $
       parseSingleSpec "assert myabs :: Int -> PosInt" @?==
          "assert myabs :: lq_tmp$db##0:Int -> PosInt"

    , testCase "autosize" $
       parseSingleSpec "autosize List" @?==
            "autosize List"

    , testCase "local" $
       parseSingleSpec "local foo :: Nat -> Nat" @?==
            "local assert foo :: lq_tmp$db##0:Nat -> Nat"

    , testCase "axiomatize" $
       parseSingleSpec "axiomatize fibA" @?==
            "reflect fibA"

    , testCase "reflect" $
       parseSingleSpec "reflect map" @?==
            "reflect map"

    , testCase "measure HMeas" $
       parseSingleSpec "measure isAbs" @?==
          "measure isAbs"

    , testCase "measure Meas" $
       parseSingleSpec "measure fv :: Expr -> (Set Bndr)" @?==
          "measure fv :: lq_tmp$db##0:Expr -> (Set Bndr)"

    , testCase "define" $
       parseSingleSpec "define $ceq = eqN" @?==
          "define $ceq = eqN"

    , testCase "infixl" $
       parseSingleSpec "infixl 9 +++" @?==
            "fixity"

    , testCase "infixr" $
       parseSingleSpec "infixr 9 +++" @?==
            "fixity"

    , testCase "infix" $
       parseSingleSpec "infix 9 +++" @?==
            "fixity"

    , testCase "inline" $
       parseSingleSpec "inline eqelems" @?==
            "inline eqelems"

    , testCase "bound PBound" $
       parseSingleSpec "bound Foo = true" @?==
          "bound Foo forall [] . [] =  true"

    , testCase "bound HBound" $
       parseSingleSpec "bound step" @?==
            "bound step"

    , testCase "class measure" $
       parseSingleSpec "class measure sz :: forall a. a -> Int" @?==
            "class measure sz :: forall a . lq_tmp$db##0:a -> Int"

    , testCase "instance measure" $
       parseSingleSpec "instance measure sz :: MList a -> Int" @?==
            "instance  measure sz :: lq_tmp$db##0:(MList a) -> Int"

    , testCase "instance" $
       parseSingleSpec "instance VerifiedNum Int where\n  - :: x:Int -> y:Int -> OkInt {x - y} " @?==
          "instance (VerifiedNum Int) where\n    - :: x:Int -> y:Int -> (OkInt {x - y})"

    , testCase "class" $
       parseSingleSpec "class Sized s where\n  size :: forall a. x:s a -> {v:Nat | v = sz x}" @?==
            "class  (Sized s) where\n    size :: forall a . x:s a -> {v : Nat | v == sz x}"

    , testCase "import" $
       parseSingleSpec "import Foo" @?==
          "import Foo"

    , testCase "data variance" $
       parseSingleSpec "data variance IO bivariant" @?==
          "data variance IO Bivariant"

    , testCase "data" $
       parseSingleSpec "data Bob = B {foo :: Int}" @?==
          "data Bob  [] =\n    | B :: forall . foo : Int -> *"

    , testCase "newtype" $
       parseSingleSpec "newtype Foo = Bar {x :: Nat}" @?==
          "newtype data Foo  [] =\n            | Bar :: forall . x : Nat -> *"

    , testCase "include" $
       parseSingleSpec "include <listSet.hquals>" @?==
            "include <listSet.hquals>"

    , testCase "invariant" $
       parseSingleSpec "invariant {v:Tree a | 0 <= ht v}" @?==
            "invariant {v : (Tree a) | 0 <= ht v}"

    , testCase "using" $
       parseSingleSpec "using (Tree a) as  {v:Tree a   | 0 <= height v}" @?==
            "using (Tree a) as {v : (Tree a) | 0 <= height v}"

    , testCase "type" $
       parseSingleSpec "type PosInt = {v: Int | v >= 0}" @?==
            "type PosInt  =  {v : Int | v >= 0}"

    , testCase "predicate" $
       parseSingleSpec "predicate Pos X  = X > 0" @?==
            "predicate Pos X  =  X > 0"

    , testCase "expression" $
       parseSingleSpec "expression Avg Xs = ((sumD Xs) / (lenD Xs))" @?==
          "predicate Avg Xs  =  sumD Xs / lenD Xs"

    , testCase "embed" $
       parseSingleSpec "embed Set as Set_Set" @?==
          "embed Set as Set_Set"

    , testCase "qualif" $
       parseSingleSpec "qualif Foo(v:Int): v < 0" @?==
          "qualif Foo defined at \"<test>\" (line 1, column 8)"

    , testCase "decrease" $
       parseSingleSpec "decrease insert 3" @?==
          "decreasing insert [2]"

    , testCase "lazyvar" $
       parseSingleSpec "lazyvar z" @?==
          "lazyvar z"

    , testCase "lazy" $
       parseSingleSpec "lazy eval" @?==
          "lazy eval"

    , testCase "default parser (Asrts)" $
       parseSingleSpec " assumeIndices :: t:ByteStringNE -> s:BS.ByteString -> [OkPos t s]" @?==
            "assumeIndices :: t:ByteStringNE -> s:BS.ByteString -> [(OkPos t s)]"
    ]

-- ---------------------------------------------------------------------

-- Test that haskell functions having the same name as liquidhaskell keywords are parsed correctly
testReservedAliases :: TestTree
testReservedAliases =
  testGroup "reserved aliases"
    [ testCase "assume" $
       parseSingleSpec "assume :: Int -> Bool " @?==
            "assume :: lq_tmp$db##0:Int -> Bool"

    , testCase "assert" $
       parseSingleSpec "assert :: Int -> Bool " @?==
            "assert :: lq_tmp$db##0:Int -> Bool"

    , testCase "autosize" $
       parseSingleSpec "autosize :: Int -> Bool " @?==
            "autosize :: lq_tmp$db##0:Int -> Bool"

    , testCase "axiomatize" $
       parseSingleSpec "axiomatize :: Int -> Bool " @?==
            "axiomatize :: lq_tmp$db##0:Int -> Bool"

    , testCase "reflect" $
       parseSingleSpec "reflect :: Int -> Bool " @?==
            "reflect :: lq_tmp$db##0:Int -> Bool"

    , testCase "measure" $
       parseSingleSpec "measure :: Int -> Bool " @?==
            "measure :: lq_tmp$db##0:Int -> Bool"

    , testCase "define 1" $
       parseSingleSpec "define :: Int -> Bool " @?==
            "define :: lq_tmp$db##0:Int -> Bool"

    , testCase "define 2" $
       parseSingleSpec "define GHC.Types.True = (true)" @?==
            "define GHC.Types.True = (true)"

    , testCase "defined" $
       parseSingleSpec "defined :: Int -> Bool " @?==
            "defined :: lq_tmp$db##0:Int -> Bool"

    , testCase "inline" $
       parseSingleSpec "inline :: Int -> Bool " @?==
            "inline :: lq_tmp$db##0:Int -> Bool"

    , testCase "bound" $
       parseSingleSpec "bound :: Int -> Bool " @?==
            "bound :: lq_tmp$db##0:Int -> Bool"

    , testCase "invariant" $
       parseSingleSpec "invariant :: Int -> Bool " @?==
            "invariant :: lq_tmp$db##0:Int -> Bool"

    , testCase "predicate" $
       parseSingleSpec "predicate :: Int -> Bool " @?==
            "predicate :: lq_tmp$db##0:Int -> Bool"

    , testCase "expression" $
       parseSingleSpec "expression :: Int -> Bool " @?==
            "expression :: lq_tmp$db##0:Int -> Bool"

    , testCase "embed" $
       parseSingleSpec "embed :: Int -> Bool " @?==
            "embed :: lq_tmp$db##0:Int -> Bool"

    , testCase "qualif" $
       parseSingleSpec "qualif :: Int -> Bool " @?==
            "qualif :: lq_tmp$db##0:Int -> Bool"
    ]

-- ---------------------------------------------------------------------

testSucceeds :: TestTree
testSucceeds =
  testGroup "Should succeed"
    [ testCase "x :: Int" $
       (parseSingleSpec "x :: Int") @?==
          "x :: Int" 

    , testCase "x :: a" $
       (parseSingleSpec "x :: a") @?==
          "x :: a" 

    , testCase "x :: a -> a" $
       (parseSingleSpec "x :: a -> a") @?==
          "x :: lq_tmp$db##0:a -> a"

    , testCase "x :: Int -> Int" $
       (parseSingleSpec "x :: Int -> Int") @?==
          "x :: lq_tmp$db##0:Int -> Int"

    , testCase "k:Int -> Int" $
       (parseSingleSpec "x :: k:Int -> Int") @?==
          "x :: k:Int -> Int"

    , testCase "type spec 1 " $
       parseSingleSpec "type IncrListD a D = [a]<{\\x y -> (x+D) <= y}>" @?==
          "type IncrListD a D  =  [a]<\\x##2 VV -> {y##3 : LIQUID$dummy | x##2 + D <= y##3}>"

    , testCase "type spec 2 " $
       parseSingleSpec "takeL :: Ord a => x:a -> [a] -> [{v:a|v<=x}]" @?==
          "takeL :: (Ord a) -> x:a -> lq_tmp$db##1:[a] -> [{v : a | v <= x}]"

    , testCase "type spec 3" $
       parseSingleSpec "bar :: t 'Nothing" @?==
          "bar :: t Nothing"

    , testCase "type spec 4" $
       parseSingleSpec "Cons :: forall <l>.a -> L^l a -> L^l a" @?==
          "Cons :: forall <l>. lq_tmp$db##0:a -> lq_tmp$db##1:(L a) -> (L a)"

    , testCase "type spec 5" $
       parseSingleSpec "mapKeysWith :: (Ord k2) => (a -> a -> a) -> (k1->k2) -> OMap k1 a -> OMap k2 a" @?==
          "mapKeysWith :: (Ord k2) -> lq_tmp$db##2:(lq_tmp$db##3:a -> lq_tmp$db##4:a -> a) -> lq_tmp$db##6:(lq_tmp$db##7:k1 -> k2) -> lq_tmp$db##9:(OMap k1 a) -> (OMap k2 a)"

    , testCase "type spec 6 " $
       parseSingleSpec (unlines $
         [ "data Tree [ht] a = Nil"
         , "            | Tree { key :: a"
         , "                   , l   :: Tree {v:a | v < key }"
         , "                   , r   :: Tree {v:a | key < v }"
         , "                   }" ])
        @?==
    --      "data Tree [ht] [a] =\n    | Tree :: forall a . key : a ->l : (Tree {v : a | v < key}) ->r : (Tree {v : a | key < v}) -> *\n    | Nil :: forall a . -> *"
          "data Tree [ht] [a] = \ 
           \     | Nil :: forall a . -> * \
           \     | Tree :: forall a . key : a ->l : (Tree {v : a | v < key}) ->r : (Tree {v : a | key < v}) -> *"    

    , testCase "type spec 7" $
       parseSingleSpec "type AVLL a X    = AVLTree {v:a | v < X}" @?==
         "type AVLL a X  =  (AVLTree {v : a | v < X})"

    , testCase "type spec 8" $
       parseSingleSpec "type AVLR a X    = AVLTree {v:a |X< v} " @?==
         "type AVLR a X  =  (AVLTree {v : a | X < v})"

    , testCase "type spec 9 " $
       parseSingleSpec (unlines $
      [ "assume (++) :: forall <p :: a -> Bool, q :: a -> Bool, r :: a -> Bool>."
      , "  {x::a<p> |- a<q> <: {v:a| x <= v}} "
      , "  {a<p> <: a<r>} "
      , "  {a<q> <: a<r>} "
      , "  Ord a => OList (a<p>) -> OList (a<q>) -> OList a<r> "])
        @?==
          "assume (++) :: forall <p :: a -> Bool, q :: a -> Bool, r :: a -> Bool> .\n               (Ord a) =>\n               {x :: {VV : a<p> | true} |- {VV : a<q> | true} <: {v : a | x <= v}} =>\n               {|- {VV : a<p> | true} <: {VV : a<r> | true}} =>\n               {|- {VV : a<q> | true} <: {VV : a<r> | true}} =>\n               lq_tmp$db##13:(OList {VV : a<p> | true}) -> lq_tmp$db##15:(OList {VV : a<q> | true}) -> (OList {VV : a<r> | true})"

    , testCase "type spec 10" $
       parseSingleSpec (unlines $
          [ "data AstF f <ix :: AstIndex -> Bool>"
          , "  = Lit Int    (i :: AstIndex<ix>)"
          , "  | Var String (i :: AstIndex<ix>)"
          , "  | App (fn :: f) (arg :: f)"
          , "  | Paren (ast :: f)" ])
          @?==
            "data AstF [f] =    \
            \   | App :: forall f . fn : f ->arg : f -> * \
            \   | Lit :: forall f . lq_tmp$db##2 : (Int (AstIndex <{VV : _<ix> | true}>)) -> *  \
            \   | Paren :: forall f . ast : f -> * \
            \   | Var :: forall f . lq_tmp$db##5 : (String (AstIndex <{VV : _<ix> | true}>)) -> *"

    , testCase "type spec 11" $
       parseSingleSpec "assume     :: b:_ -> a -> {v:a | b} " @?==
          "assume :: b:{VV : _ | $HOLE} -> lq_tmp$db##0:a -> {v : a | b}"

    , testCase "type spec 12" $
       parseSingleSpec (unlines $
          [ "app :: forall <p :: Int -> Bool, q :: Int -> Bool>. "
          , "       {Int<q> <: Int<p>}"
          , "       {x::Int<q> |- {v:Int| v = x + 1} <: Int<q>}"
          , "       (Int<p> -> ()) -> x:Int<q> -> ()" ])
          @?==
            "app :: forall <p :: Int -> Bool, q :: Int -> Bool> .\n       {|- (Int <{VV : _<q> | true}>) <: (Int <{VV : _<p> | true}>)} =>\n       {x :: (Int <{VV : _<q> | true}>) |- {v : Int | v == x + 1} <: (Int <{VV : _<q> | true}>)} =>\n       lq_tmp$db##8:(lq_tmp$db##9:(Int <{VV : _<p> | true}>) -> ()) -> x:(Int <{VV : _<q> | true}>) -> ()"

    , testCase "type spec 13" $
       parseSingleSpec (unlines $
          [ " ssum :: forall<p :: a -> Bool, q :: a -> Bool>. "
          , "         {{v:a | v == 0} <: a<q>}"
          , "         {x::a<p> |- {v:a | x <= v} <: a<q>}"
          , "         xs:[{v:a<p> | 0 <= v}] -> {v:a<q> | len xs >= 0 && 0 <= v } "])
          @?==
            "ssum :: forall <p :: a -> Bool, q :: a -> Bool> .\n        {|- {v : a | v == 0} <: {VV : a<q> | true}} =>\n        {x :: {VV : a<p> | true} |- {v : a | x <= v} <: {VV : a<q> | true}} =>\n        xs:[{v : a<p> | 0 <= v}] -> {v : a<q> | len xs >= 0\n                                                && 0 <= v}"

    , testCase "type spec 14" $
       parseSingleSpec (unlines $
          [ " predicate ValidChunk V XS N "
          , " = if len XS == 0 "
          , "     then (len V == 0) "
          , "     else (((1 < len XS && 1 < N) => (len V  < len XS)) "
          , "       && ((len XS <= N ) => len V == 1)) "])
          @?==
          "predicate ValidChunk V  XS  N  =  (len XS == 0 => len V == 0)\n                                  && (not (len XS == 0) => (1 < len XS\n                                                            && 1 < N => len V < len XS)\n                                                           && (len XS <= N => len V == 1))"


    , testCase "type spec 15" $
       parseSingleSpec "assume (=*=.) :: Arg a => f:(a -> b) -> g:(a -> b) -> (r:a -> {f r == g r}) -> {v:(a -> b) | f == g}" @?==
            "assume (=*=.) :: (Arg a) -> f:(lq_tmp$db##1:a -> b) -> g:(lq_tmp$db##3:a -> b) -> lq_tmp$db##5:(r:a -> {VV : _ | f r == g r}) -> lq_tmp$db##6:a -> b"

    , testCase "type spec 16" $
       parseSingleSpec "sort :: (Ord a) => xs:[a] -> OListN a {len xs}" @?==
           "sort :: (Ord a) -> xs:[a] -> (OListN a {len xs})"

    , testCase "type spec 17" $
       parseSingleSpec " ==. :: x:a -> y:{a| x == y} -> {v:b | v ~~ x && v ~~ y } " @?==
            "==. :: x:a -> y:{y : a | x == y} -> {v : b | v ~~ x\n                                             && v ~~ y}"

    , testCase "type spec 18" $
       parseSingleSpec "measure snd :: (a,b) -> b" @?==
            "measure snd :: lq_tmp$db##0:(a, b) -> b"

    , testCase "type spec 19" $
       parseSingleSpec "returnST :: xState:a \n             -> ST <{\\xs xa v -> (xa = xState)}> a s " @?==
           "returnST :: xState:a -> (ST <\\xs##1 xa##2 VV -> {v##3 : LIQUID$dummy | xa##2 == xState}> a s)"

    , testCase "type spec 20" $
       parseSingleSpec "makeq :: l:_ -> r:{ _ | size r <= size l + 1} -> _ " @?==
           "makeq :: l:{VV : _ | $HOLE} -> r:{r : _ | size r <= size l + 1} -> {VV : _ | $HOLE}"

    , testCase "type spec 21" $
       parseSingleSpec "newRGRef :: forall <p :: a -> Bool, r :: a -> a -> Bool >.\n   e:a<p> ->\n  e2:a<r e> ->\n  f:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->\n IO (RGRef <p, r> a)" @?==
            "newRGRef :: forall <p :: a -> Bool, r :: a a -> Bool> .\n            e:{VV : a<p> | true} -> e2:{VV : a<r e> | true} -> f:(x:{VV : a<p> | true} -> y:{VV : a<r x> | true} -> {v : a<p> | v == y}) -> (IO (RGRef <{VV : _<p> | true}, {VV : _<r> | true}> a))"

    , testCase "type spec 22" $
       parseSingleSpec "cycle        :: {v: [a] | len(v) > 0 } -> [a]" @?==
            "cycle :: v:{v : [a] | len v > 0} -> [a]"

    , testCase "type spec 23" $
       parseSingleSpec "cons :: x:a -> _ -> {v:[a] | hd v = x} " @?==
         "cons :: x:a -> lq_tmp$db##0:{VV : _ | $HOLE} -> {v : [a] | hd v == x}"

    , testCase "type spec 24" $
       parseSingleSpec "set :: a:Vector a -> i:Idx a -> a -> {v:Vector a | vlen v = vlen a}" @?==
         "set :: a:(Vector a) -> i:(Idx a) -> lq_tmp$db##0:a -> {v : (Vector a) | vlen v == vlen a}"

    , testCase "type spec 25" $
       parseSingleSpec "assume GHC.Prim.+#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v: GHC.Prim.Int# | v = x + y}" @?==
         "assume GHC.Prim.+# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v : GHC.Prim.Int# | v == x + y}"

    , testCase "type spec 26" $
       parseSingleSpec " measure isEVar " @?==
         "measure isEVar"

    , testCase "type spec 27" $
       parseSingleSpec (unlines $
         [ "data List a where"
         , "    Nil  :: List a "
         , "  | Cons :: listHead:a -> listTail:List a -> List a  "])
        @?==
            "data List  [a] =\n    | Cons :: forall a . listHead : a ->listTail : (List a) -> (List a)\n    | Nil :: forall a . -> (List a)"

    , testCase "type spec 28" $
       parseSingleSpec (unlines $
         [ "data List2 a b <p :: a -> Bool> where"
         , "    Nil2  :: List2 a "
         , "  | Cons2 :: listHead:a -> listTail:List a -> List2 a b"])
        @?== 
           "data List2  [a, b] = \ 
            \  | Cons2 :: forall a b . listHead : a ->listTail : (List a) -> (List2 a b) \
            \  | Nil2 :: forall a b . -> (List2 a)"

    , testCase "type spec 29" $
       parseSingleSpec (unlines $
         [ "data Ev :: Peano -> Prop where"
         , "  EZ  :: Prop (Ev Z)"
         , "| ESS :: n:Peano -> Prop (Ev n) -> Prop (Ev (S (S n)))"
         ])
        @?==
            "data Ev  [] =\n    | ESS :: forall . n : Peano ->lq_tmp$db##4 : (Prop (Ev n)) -> (Prop (Ev (S (S n))))\n    | EZ :: forall . -> (Prop (Ev Z))"

    , testCase "type spec 30" $
       parseSingleSpec (unlines $
         [ "measure fst :: (a,b) -> a"
         , "fst (a,b) = a"
         ])
        @?==
            "measure fst :: lq_tmp$db##0:(a, b) -> a\n        fst ((,)a b) = a"
    ]

-- ---------------------------------------------------------------------

testFails :: TestTree
testFails =
  testGroup "Does fail"
    [ testCase "Maybe k:Int -> Int" $
          parseSingleSpec "x :: Maybe k:Int -> Int" @?==
            "<test>:1:13: Error: Cannot parse specification:\n    unexpected ':'\n    expecting monoPredicateP, bareTyArgP, mmonoPredicateP, white space, \"->\", \"~>\", \"=>\", \"/\" or end of input"
    ]


-- ---------------------------------------------------------------------

testErrorReporting :: TestTree
testErrorReporting =
  testGroup "Error reporting"
    [ testCase "assume mallocForeignPtrBytes :: n:Nat -> IO (ForeignPtrN a n " $
          parseSingleSpec "assume mallocForeignPtrBytes :: n:Nat -> IO (ForeignPtrN a n " @?==
            "<test>:1:62: Error: Cannot parse specification:\n    unexpected end of input\n    expecting bareTyArgP"

    , testCase "Missing |" $
          parseSingleSpec "ff :: {v:Nat  v >= 0 }" @?==
          -- parseSingleSpec "ff :: {v :  }" @?==
            "<test>:1:9: Error: Cannot parse specification:\n    unexpected \":\"\n    expecting operator, white space or \"}\""
    ]

-- ---------------------------------------------------------------------

-- | Parse a single type signature containing LH refinements. To be
-- used in the REPL.
parseSingleSpec :: String -> String
parseSingleSpec src = deSpace $ 
  case LH.singleSpecP (initialPos "<test>") src of
    Left err  -> show err
    Right res -> F.showpp res -- show (dummyLocs res)

gadtSpec :: String
gadtSpec = unlines
  [ "data Ev where"
  , "   EZ  :: {v:Ev | prop v = Ev Z}"
  , " | ESS :: n:Peano -> {v:Ev | prop v = Ev n} -> {v:Ev | prop v = Ev (S (S n)) }"
  ]

deSpace :: String -> String 
deSpace = filter (not . isSpace)

(@?==) :: String -> String -> Assertion 
s1 @?== s2 = (deSpace s1) @?= (deSpace s2)

------------------------------------------------------------------------

dummyLocs :: (Data a) => a -> a
dummyLocs = everywhere (mkT posToDummy)
  where
    posToDummy :: SourcePos -> SourcePos
    posToDummy _ = dummyPos "Fixpoint.Types.dummyLoc"

-- ---------------------------------------------------------------------
