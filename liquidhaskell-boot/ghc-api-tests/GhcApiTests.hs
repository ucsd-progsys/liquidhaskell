
import           Control.Monad
import           Liquid.GHC.API
    ( ApiComment(ApiBlockComment)
    , apiCommentsParsedSource
    )
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Runners.AntXML

import qualified GHC.Data.EnumSet as EnumSet
import qualified GHC.Data.FastString as GHC
import qualified GHC.Data.StringBuffer as GHC
import qualified GHC.Parser as GHC
import qualified GHC.Parser.Lexer as GHC
import qualified GHC.Types.SrcLoc as GHC

main :: IO ()
main =
  defaultMainWithIngredients (antXMLRunner:defaultIngredients) testTree

testTree :: TestTree
testTree =
    testGroup "GHC API" [
      testCase "apiComments" testApiComments
    ]

-- Tests that Liquid.GHC.API.Extra.apiComments can retrieve the comments in
-- the right order from an AST
testApiComments :: IO ()
testApiComments = do
    let str = unlines
          [ "{-@ LIQUID \"--ple\" @-}"
          , "module A where"
          , "import B"
          , ""
          , "{-@ i :: { v:Int | v>=0 } @-}"
          , "i :: Int"
          , "i = 4"
          , ""
          , "{-@ infixr ++ @-}"
          , ""
          , "{-@ abs :: Int -> { v:Int | v >= 0 } @-}"
          , "abs :: Int -> Int"
          , "abs x = z"
          , "  where"
          , "    {-@ { v: Int | z >= 0 } @-}"
          , "    z = if x < 0 then -x else x"
          ]
    lhsMod <- parseMod str "A.hs"
    let comments = map GHC.unLoc (apiCommentsParsedSource lhsMod)
        expected = map ApiBlockComment
          [ "{-@ LIQUID \"--ple\" @-}"
          , "{-@ i :: { v:Int | v>=0 } @-}"
          , "{-@ infixr ++ @-}"
          , "{-@ abs :: Int -> { v:Int | v >= 0 } @-}"
          , "{-@ { v: Int | z >= 0 } @-}"
          ]
    when (expected /= comments) $
      fail $ unlines $ "Unexpected comments:" : map show comments
  where
    parseMod str filepath = do
      let location = GHC.mkRealSrcLoc (GHC.mkFastString filepath) 1 1
          buffer = GHC.stringToStringBuffer str
          popts = GHC.mkParserOpts EnumSet.empty EnumSet.empty False True True True
          parseState = GHC.initParserState popts buffer location
      case GHC.unP GHC.parseModule parseState of
        GHC.POk _ result -> return result
        _ -> fail "Unexpected parser error"
