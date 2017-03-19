{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Applicative
import Language.Fixpoint.Parse
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.IO
import System.IO.Error
import Test.Tasty
import Test.Tasty.HUnit
import Text.Printf

main :: IO ()
main = defaultMain $ parserTests

parserTests =
  testGroup "Tests"
    [
      testSortP
    , testFunAppP
      -- testExprP
    ]

testExprP =
  testGroup "exprP"
    [ testCase "aa" $
        (show $ doParse' exprP "test" "x >= -1") @=? ""
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

testSortP =
  testGroup "SortP"
    [ testCase "FAbs" $
        show (doParse' sortP "test" "(func(1, [int; @(0)]))") @?= "FAbs 0 (FFunc FInt (FVar 0))"

    , testCase "(FAbs)" $
        show (doParse' sortP "test" "((func(1, [int; @(0)])))") @?= "FAbs 0 (FFunc FInt (FVar 0))"

    , testCase "FApp FInt" $
        show (doParse' sortP "test" "[int]") @?=
              "FApp (FTC (TC dummyLoc (TCInfo {tc_isNum = False, tc_isReal = False, tc_isString = False}))) FInt"

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
             "FTC (TC dummyLoc (TCInfo {tc_isNum = False, tc_isReal = False, tc_isString = True}))"

    , testCase "SYMBOL" $
        show (doParse' sortP "test" "F#y") @?=
             "FTC (TC \"F#y\" defined from: \"test\" (line 1, column 1) to: \"test\" (line 1, column 4) (TCInfo {tc_isNum = False, tc_isReal = False, tc_isString = False}))"

    , testCase "FVar 3" $
        show (doParse' sortP "test" "@(3)") @?= "FVar 3"

    , testCase "FObj " $
        show (doParse' sortP "test" "foo") @?= "FObj \"foo\""
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
