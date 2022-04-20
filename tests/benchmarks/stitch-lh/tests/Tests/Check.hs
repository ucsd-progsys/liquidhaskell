{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--ple" @-}
module Tests.Check where

import Prelude hiding ( lex )

import qualified Data.Map as Map -- XXX: Needed for LH
import Language.Stitch.LH.Check
import qualified Language.Stitch.LH.Data.List as List -- XXX: Needed for LH
import Language.Stitch.LH.Parse
import Language.Stitch.LH.Lex
import Language.Stitch.LH.Check
import Language.Stitch.LH.Type
import Language.Stitch.LH.Eval
import Language.Stitch.LH.Util

import Control.Monad.Trans.Except
import Control.Monad.Reader

import Text.PrettyPrint.ANSI.Leijen

import Data.Maybe
import Data.List as List
import qualified Data.Set as Set -- XXX: Needed for LH
import qualified Control.Arrow as Arrow

import Test.Tasty
import Test.Tasty.HUnit

checkTestCases :: [(String, Maybe (String, Ty, String))]
checkTestCases = [ ("1", Just ("1", TInt, "1"))
                 , ("1 + true", Nothing)
                 , ("(\\x:Int.x) 5",
                    Just ("(λ#:Int. #0) 5", TInt, "5"))
                 , ("(\\x:Int.\\y:Int->Int.y x) 4 (\\z:Int.z*2)",
                    Just ("(λ#:Int. λ#:Int -> Int. #0 #1) 4 (λ#:Int. #0 * 2)",
                          TInt, "8"))
                 , ("1 + 2 * 3 / 4 - 10 % 3",
                    Just ("1 + 2 * 3 / 4 - 10 % 3", TInt, "1"))
                 , ("if true then 1 else false", Nothing)
                 , ("if 3 - 1 == 2 then \\x:Int.x else \\x:Int.3",
                    Just ("if 3 - 1 == 2 then λ#:Int. #0 else λ#:Int. 3",
                          TFun TInt TInt, "λ#:Int. #0"))
                 , ("1 > 2", Just ("1 > 2", TBool, "false"))
                 , ("2 > 1", Just ("2 > 1", TBool, "true"))
                 , ("1 > 1", Just ("1 > 1", TBool, "false"))
                 , ("1 >= 1", Just ("1 >= 1", TBool, "true"))
                 , ("1 < 2", Just ("1 < 2", TBool, "true"))
                 , ("1 < 1", Just ("1 < 1", TBool, "false"))
                 , ("1 <= 1", Just ("1 <= 1", TBool, "true"))
                 , ("id_int (id_int 5)", Just ("(λ#:Int. #0) ((λ#:Int. #0) 5)", TInt, "5"))
                 ]

checkTests :: TestTree
checkTests = testGroup "Typechecker" $
  List.map (\(expr_str, m_result) ->
               testCase ("`" ++ expr_str ++ "'") $
               (case do
                       uexp <- Arrow.left text $ parseExp =<< lex expr_str
                       Arrow.left pretty $ check id_globals uexp $ \exp sty -> return $
                         case m_result of
                           Just result
                             -> (render (plain $ pretty (ScopedExp 0 exp)), sty,
                                 render (plain $ pretty (eval exp)))
                                 @?= result
                           _ -> assertFailure "unexpected type-check success"
                  of
                  Left _  -> assertBool "unexpected failure" (isNothing m_result)
                  Right b -> b)) checkTestCases

id_globals :: Globals
id_globals = extendGlobals "id_int" (TypedExp (Lam TInt (Var TInt 0)) (TFun TInt TInt)) emptyGlobals
