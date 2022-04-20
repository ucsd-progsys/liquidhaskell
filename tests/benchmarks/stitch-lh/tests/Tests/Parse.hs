module Tests.Parse where

import Language.Stitch.LH.Lex
import Language.Stitch.LH.Parse
import Language.Stitch.LH.Unchecked
import Language.Stitch.LH.Util
import Tests.Util

import Prelude hiding ( lex )

import Text.PrettyPrint.ANSI.Leijen

import Data.List as List

parseTestCases :: [(String, String)]
parseTestCases = [ ("\\x:Int.x", "λ#:Int. #0")
                 , ("\\x:Int.\\y:Int.x", "λ#:Int. λ#:Int. #1")
                 , ("\\x:Int.\\x:Int.x", "λ#:Int. λ#:Int. #0")
                 , ("1 + 2 + 3", "1 + 2 + 3")
                 , ("1 + 2 * 4 % 5", "1 + 2 * 4 % 5")
                 , ("if \\x:Int.x then 4 else (\\x:Int.x) (\\y:Int.y)",
                    "if λ#:Int. #0 then 4 else (λ#:Int. #0) (λ#:Int. #0)")
                 , ("true true true", "true true true")
                 , ("true false (\\x:Int.x)", "true false (λ#:Int. #0)")
                 , ("\\x:Int->Int.\\y:Int.x y", "λ#:Int -> Int. λ#:Int. #1 #0")
                 , ("if 3 - 1 == 2 then \\x:Int.x else \\x:Int.3",
                    "if 3 - 1 == 2 then λ#:Int. #0 else λ#:Int. 3")
                 , ("\\x:Int.y", "λ#:Int. y")
                 ]

parserFailTestCases :: [String]
parserFailTestCases = [ " {- "
                      , "{-{- -}" ]

parseTests :: TestTree
parseTests = testGroup "Parser"
  [ testGroup "Success" $
    List.map (\(str, out) -> testCase ("`" ++ str ++ "'") $
              (render $ plain $ pretty (fmap (ScopedUExp 0) $ parseExp =<< lex str)) @?=
                ("Right " ++ out))
             parseTestCases
  , testGroup "Failure" $
    List.map (\str -> testCase ("`" ++ str ++ "'") $
              (case parseExp =<< lex str of Left _ -> True; _ -> False) @?
              "parse erroneously successful")
             parserFailTestCases ]
