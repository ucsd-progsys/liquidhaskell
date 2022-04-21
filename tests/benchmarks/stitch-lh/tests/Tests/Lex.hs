module Tests.Lex where

import Language.Stitch.LH.Lex
import Language.Stitch.LH.Token
import Language.Stitch.LH.Op
import Tests.Util

import Prelude hiding ( lex )

import Data.List as List
import Control.Arrow as Arrow ( right )

lexTestCases :: [(String, [Token])]
lexTestCases = [ ("", [])
               , ("  ", [])
               , (" {- hi -}  \n  ", [])
               , (" {----} ", [])
               , (" {- foo {- bar -} blah -}", [])
               , (" {- foo {-- bar -}-}", [])
               , ("{- blah ---}", [])
               , ("{- froggle -} -- blah", [])
               , ("x", [Name "x"])
               , ("(()", [LParen, LParen, RParen])
               , ("++--++", [ArithOp Plus, ArithOp Plus])
               , ("->->", [ArrowTok, ArrowTok])
               , ("45+332-89/1*3%xyz", [ IntTok 45, ArithOp Plus, IntTok 332
                                       , ArithOp Minus, IntTok 89, ArithOp Divide
                                       , IntTok 1, ArithOp Times, IntTok 3
                                       , ArithOp Mod, Name "xyz" ])
               , ("===", [ArithOp Equals, Assign])
               , ("if x then y else z", [If, Name "x", Then, Name "y", Else, Name "z"])
               , ("ifs trues falsee true-", [ Name "ifs", Name "trues", Name "falsee"
                                            , BoolTok True, ArithOp Minus ])
               , (":\\", [Colon, Lambda])
               , (">>==<===<", [ ArithOp Greater, ArithOp GreaterE, Assign
                               , ArithOp LessE, ArithOp Equals, ArithOp Less ])
               ]

lexTests :: TestTree
lexTests = testGroup "Lexer" $
  List.map (\(str, out) -> testCase ("`" ++ str ++ "'") $
                           Arrow.right (List.map unLoc)
                                        (lex str) @?= Right out)
           lexTestCases
