{-# LANGUAGE OverloadedStrings #-}

module Main where

import Language.Fixpoint.Types (showFix)
import Language.Fixpoint.Parse
import Test.Tasty
import Test.Tasty.HUnit
import Data.List (intercalate)

main :: IO ()
main = defaultMain $ parserTests

parserTests :: TestTree
parserTests =
  testGroup "Tests"
    [ testSortP
    , testFunAppP
    , testExpr0P
    , testPredP
    , testDeclP
    ]

-- ---------------------------------------------------------------------
{-

sort = '(' sort ')'
     | 'func' funcSort
     | '[' sort ']'
     | bvsort
     | fTyCon
     | tVar

sorts = '[' sortslist ']'

sortslist = sort
          | sort `;` sortslist

funcSort = '(' int `,` sorts ')'

     e.g.(func(1, [int; @(0)]))

bvsort = '(' 'BitVec' 'Size32' ')'
       | '(' 'BitVec' 'Size64' ')'

fTyCon = 'int' | 'Integer' | 'Int' | 'real' | 'num' | 'Str'
       | SYMBOL

SYMBOL = upper case char or _, followed by many of '%' '#' '$' '\'

tVar = '@' varSort
     | LOWERID

varSort = '(' INT ')'
-}

testSortP :: TestTree
testSortP =
  testGroup "SortP"
    [ testCase "FAbs" $
        show (doParse' sortP "test" "(func(1, [int; @(0)]))") @?= "FAbs 0 (FFunc FInt (FVar 0))"

    , testCase "(FAbs)" $
        show (doParse' sortP "test" "((func(1, [int; @(0)])))") @?= "FAbs 0 (FFunc FInt (FVar 0))"

    , testCase "FApp FInt" $
        show (doParse' sortP "test" "[int]") @?=
              "FApp (FTC (TC \"[]\" (dummyLoc) (TCInfo {tc_isNum = False, tc_isReal = False, tc_isString = False}))) FInt"

    , testCase "bv32" $
        show (doParse' sortP "test" "BitVec Size32") @?=
              "FApp (FTC (TC \"BitVec\" defined from: \"test\" (line 1, column 1) to: \"test\" (line 1, column 8) (TCInfo {tc_isNum = False, tc_isReal = False, tc_isString = False}))) (FTC (TC \"Size32\" defined from: \"test\" (line 1, column 8) to: \"test\" (line 1, column 14) (TCInfo {tc_isNum = False, tc_isReal = False, tc_isString = False})))"

    , testCase "bv64" $
        show (doParse' sortP "test" "BitVec Size64") @?=
              "FApp (FTC (TC \"BitVec\" defined from: \"test\" (line 1, column 1) to: \"test\" (line 1, column 8) (TCInfo {tc_isNum = False, tc_isReal = False, tc_isString = False}))) (FTC (TC \"Size64\" defined from: \"test\" (line 1, column 8) to: \"test\" (line 1, column 14) (TCInfo {tc_isNum = False, tc_isReal = False, tc_isString = False})))"

    , testCase "FInt int" $
        show (doParse' sortP "test" "int") @?= "FInt"

    , testCase "FInt Integer" $
        show (doParse' sortP "test" "Integer") @?= "FInt"

    , testCase "FInt Int" $
        show (doParse' sortP "test" "Int") @?= "FInt"

    , testCase "FReal real" $
        show (doParse' sortP "test" "real") @?= "FReal"

    , testCase "FNum num" $
        show (doParse' sortP "test" "num") @?= "FNum"

    , testCase "FStr" $
        show (doParse' sortP "test" "Str") @?=
             "FTC (TC \"Str\" (dummyLoc) (TCInfo {tc_isNum = False, tc_isReal = False, tc_isString = True}))"

    , testCase "SYMBOL" $
        show (doParse' sortP "test" "F#y") @?=
             "FTC (TC \"F#y\" defined from: \"test\" (line 1, column 1) to: \"test\" (line 1, column 4) (TCInfo {tc_isNum = False, tc_isReal = False, tc_isString = False}))"

    , testCase "FVar 3" $
        show (doParse' sortP "test" "@(3)") @?= "FVar 3"

    , testCase "FObj " $
        show (doParse' sortP "test" "foo") @?= "FObj \"foo\""

    , testCase "FObj " $
        show (doParse' sortP "test" "_foo") @?= "FObj \"_foo\""

    , testCase "Coerce0" $
        show (doParse' predP "test" "v = (coerce (a ~ int) (f x))")
          @?= "PAtom Eq (EVar \"v\") (ECoerc (FObj \"a\") FInt (EApp (EVar \"f\") (EVar \"x\")))"
    ]

-- ---------------------------------------------------------------------
{-

funApp = lit
       | exprFunSpaces
       | expFunSemis
       | expFunCommas
       | simpleApp

lit = 'lit' stringLiteral sort

exprFunSpaces =

exprFunSemis =

exprFunCommas =

simpleApp =
-}
testFunAppP :: TestTree
testFunAppP =
  testGroup "FunAppP"
    [ testCase "ECon (litP)" $
        show (doParse' funAppP "test" "lit \"#x00000008\" (BitVec  Size32)") @?=
          "ECon (L \"#x00000008\" (FApp (FTC (TC \"BitVec\" defined from: \"test\" (line 1, column 19) to: \"test\" (line 1, column 27) (TCInfo {tc_isNum = False, tc_isReal = False, tc_isString = False}))) (FTC (TC \"Size32\" defined from: \"test\" (line 1, column 27) to: \"test\" (line 1, column 33) (TCInfo {tc_isNum = False, tc_isReal = False, tc_isString = False})))))"

    , testCase "ECon (exprFunSpacesP)" $
        show (doParse' funAppP "test" "fooBar baz qux") @?= "EApp (EApp (EVar \"fooBar\") (EVar \"baz\")) (EVar \"qux\")"

    , testCase "ECon (exprFunCommasP)" $
        show (doParse' funAppP "test" "fooBar (baz, qux)") @?= "EApp (EApp (EVar \"fooBar\") (EVar \"baz\")) (EVar \"qux\")"

    , testCase "ECon (exprFunSemisP)" $
        show (doParse' funAppP "test" "fooBar ([baz; qux])") @?= "EApp (EApp (EVar \"fooBar\") (EVar \"baz\")) (EVar \"qux\")"

    , testCase "ECon (simpleAppP)" $
        show (doParse' funAppP "test" "fooBar (baz + 1)") @?= "EApp (EVar \"fooBar\") (EBin Plus (EVar \"baz\") (ECon (I 1)))"
    ]

-- ---------------------------------------------------------------------
{-
expr0 = fastIf
      | symconst
      | constant
      | '_|_'
      | lam
      | '(' expr ')'
      | '(' exprCast ')'
      | symChars

-}
testExpr0P :: TestTree
testExpr0P =
  testGroup "expr0P"
    [ testCase "EIte" $
        show (doParse' expr0P "test" "if true then x else y") @?= "EIte (PAnd []) (EVar \"x\") (EVar \"y\")"

    , testCase "ESym SL" $
        show (doParse' expr0P "test" "\"foo\" ") @?= "ESym (SL \"foo\")"

    , testCase "ECon R" $
        show (doParse' expr0P "test" "0.0") @?= "ECon (R 0.0)"

    , testCase "ECon I" $
        show (doParse' expr0P "test" "0") @?= "ECon (I 0)"

    , testCase "ECon I" $
        show (doParse' expr0P "test" "0") @?= "ECon (I 0)"

    , testCase "EBot / POr []" $
        show (doParse' expr0P "test" "_|_") @?= "POr []" -- pattern for "EBot"

    , testCase "ELam" $
        show (doParse' expr0P "test" "\\ foo : Int -> true") @?= "ELam (\"foo\",FInt) (PAnd [])"

    , testCase "Expr" $
        show (doParse' expr0P "test" "(1)") @?= "ECon (I 1)"

    , testCase "ECst dcolon" $
        show (doParse' expr0P "test" "(1 :: Int)") @?= "ECst (ECon (I 1)) FInt"

    , testCase "ECst colon" $
        show (doParse' expr0P "test" "(1 : Int)") @?= "ECst (ECon (I 1)) FInt"

    , testCase "charsExpr EVar" $
        show (doParse' expr0P "test" "foo") @?= "EVar \"foo\""

    , testCase "charsExpr ECon" $
        show (doParse' expr0P "test" "1") @?= "ECon (I 1)"
    ]

-- ---------------------------------------------------------------------
{-

pred = expressionParse (prefixOp++infixOp) pred0

prefixOp = '~' | 'not'

infixOp  = '&&' | '||' | '=>' | '==>' | '<=>'

-- terms are pred0
pred0 = 'true' | 'false'
      | '??'
      | kvarPred
      | fastIfP
      | predr
      | '(' pred ')'
      | '?' expr
      | funApp
      | symbol
      | '&&' preds
      | '||' preds

kvarPred = kvar substs

kvar = '$' symbol

substs = {- empty -}
       | subst substs

subst = '[' symbol ':=' expr ']'

preds = '[' predslist ']'

predslist = pred
          | pred `;` predslist

fastIf = 'if' pred 'then' pred 'else' pred

predr = expr brel expr

brelP = '==' | '=' | '~~' | '!=' | '/=' | '!~' | '<' | '<=' | '>' | '>='

-}

testPredP :: TestTree
testPredP =
  testGroup "predP"
    [ testCase "PTrue" $
        show (doParse' predP "test" "true") @?= "PAnd []" -- pattern for PTrue

    , testCase "PFalse" $
        show (doParse' predP "test" "false") @?= "POr []" -- pattern for PFalse

   --     , testCase "PGrad / ??" $
   --       show (doParse' predP "test" "??") @?= "PGrad $\"\\\"test\\\" (line 1, column 3)\"  (PAnd [])"
   --   "PGrad $\"\\\"test\\\" (line 1, column 3)\"  (GradInfo {gsrc = SS {sp_start = \"test\" (line 1, column 3), sp_stop = \"test\" (line 1, column 3)}, gused = Nothing}) (PAnd [])"

    , testCase "kvarPred empty" $
        show (doParse' predP "test" "$foo") @?= "PKVar $\"foo\" "

    , testCase "kvarPred one" $
        show (doParse' predP "test" "$foo  [x := 1]") @?= "PKVar $\"foo\" [x:=1]"

    , testCase "kvarPred two" $
        show (doParse' predP "test" "$foo  [x := 1] [ y := true ]") @?= "PKVar $\"foo\" [x:=1][y:=true]"

    , testCase "fastIf" $
        show (doParse' predP "test" "if true then true else false" ) @?=
          -- note conversion
          "PAnd [PImp (PAnd []) (PAnd []),PImp (PNot (PAnd [])) (POr [])]"

    , testCase "brel" $
        show (doParse' predP "test" "1 == 2") @?= "PAtom Eq (ECon (I 1)) (ECon (I 2))"

    , testCase "parens pred" $
        show (doParse' predP "test" "((1 == 2))") @?= "PAtom Eq (ECon (I 1)) (ECon (I 2))"

    , testCase "? expr" $
        show (doParse' predP "test" "? (1+2)") @?= "EBin Plus (ECon (I 1)) (ECon (I 2))"

    , testCase "funApp 1" $
        show (doParse' predP "test" "f a b") @?= "EApp (EApp (EVar \"f\") (EVar \"a\")) (EVar \"b\")"

    , testCase "funApp 2" $
        show (doParse' predP "test" "f (a, b)") @?= "EApp (EApp (EVar \"f\") (EVar \"a\")) (EVar \"b\")"

    , testCase "funApp 3" $
        show (doParse' predP "test" "f ([a; b])") @?= "EApp (EApp (EVar \"f\") (EVar \"a\")) (EVar \"b\")"

    , testCase "symbol" $
        show (doParse' predP "test" "f") @?= "EVar \"f\""

    , testCase "&& 0" $
        show (doParse' predP "test" "&& []") @?= "PAnd []"

    , testCase "&& 1" $
        show (doParse' predP "test" "&& [x]") @?= "PAnd [EVar \"x\"]"

    , testCase "&& 2" $
        show (doParse' predP "test" "&& [x;y]") @?= "PAnd [EVar \"x\",EVar \"y\"]"

    , testCase "|| 0" $
        show (doParse' predP "test" "|| []") @?= "POr []"

    , testCase "|| 1" $
        show (doParse' predP "test" "|| [x]") @?= "POr [EVar \"x\"]"

    , testCase "|| 2" $
        show (doParse' predP "test" "|| [x;y]") @?= "POr [EVar \"x\",EVar \"y\"]"
    ]


{-

data Vec 1 = [
    Nil {}
  | Cons { vHead : @(0), vTail : Vec @(0)}
  ]

-}

testDeclP :: TestTree
testDeclP = testGroup "dataDeclP"
  [ mkT "fld0"  dataFieldP fld0
  , mkT "fld1"  dataFieldP fld1
  , mkT "fld2"  dataFieldP fld2
  , mkT "ctor0" dataCtorP  ctor0
  , mkT "ctor1" dataCtorP  ctor1
  , mkT "decl0" dataDeclP decl0
  ]
  where
    mkT name p t = testCase name $ showFix (doParse' p "test" t) @?= t
    fld0    = "vHead : int"
    fld1    = "vHead : @(0)"
    fld2    = "vTail : (Vec @(0))"
    ctor0   = "nil {}"
    ctor1   = "cons {vHead : @(0), vTail : (Vec @(0))}"
    decl0   = intercalate "\n"
                [ "Vec 1 = ["
                , "  | nil {}"
                , "  | cons {vHead : @(0), vTail : Vec}"
                , "]"
                ]
