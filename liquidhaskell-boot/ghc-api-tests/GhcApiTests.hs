{-# LANGUAGE ViewPatterns #-}

import           Control.Monad
import           Control.Monad.IO.Class (liftIO)
import           Data.List (find)
import           Data.Time (getCurrentTime)
import           Liquid.GHC.API
    ( ApiComment(ApiBlockComment)
    , Expr(..)
    , Alt(..)
    , AltCon(..)
    , LitNumType(..)
    , Literal(..)
    , apiCommentsParsedSource
    , occNameString
    , pAT_ERROR_ID
    , showPprQualified
    , splitDollarApp
    , untick
    )
import           Liquid.GHC.API.Extra (addNoInlinePragmasToBinds)
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Runners.AntXML

import qualified GHC as GHC
import qualified GHC.Builtin.Names as GHC
import qualified GHC.Builtin.Types as GHC
import qualified GHC.Core as GHC
import qualified GHC.Data.EnumSet as EnumSet
import qualified GHC.Data.FastString as GHC
import qualified GHC.Data.StringBuffer as GHC
import qualified GHC.Driver.Main as GHC (hscDesugar)
import qualified GHC.Parser as Parser
import qualified GHC.Parser.Lexer as GHC
import qualified GHC.Types.Id as GHC
import qualified GHC.Types.Name as GHC
import qualified GHC.Types.SrcLoc as GHC
import qualified GHC.Unit.Module.ModGuts as GHC
import qualified GHC.Unit.Types as GHC
import qualified GHC.Utils.Error as GHC

import GHC.Paths (libdir)


main :: IO ()
main =
  defaultMainWithIngredients (antXMLRunner:defaultIngredients) testTree

testTree :: TestTree
testTree =
    testGroup "GHC API"
      [ testCase "apiComments" testApiComments
      , testCase "caseDesugaring" testCaseDesugaring
      , testCase "numericLiteralDesugaring" testNumLitDesugaring
      , testCase "dollarDesugaring" testDollarDesugaring
      , testCase "deadBindingPreservation" testDeadBindingPreservation
      , testCase "exportedBindingNotInlined" testExportedBindingNotInlined
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
          popts = GHC.mkParserOpts EnumSet.empty GHC.emptyDiagOpts False True True True
          parseState = GHC.initParserState popts buffer location
      case GHC.unP Parser.parseModule parseState of
        GHC.POk _ result -> return result
        _ -> fail "Unexpected parser error"

-- | Tests that case expressions desugar as Liquid Haskell expects.
testCaseDesugaring :: IO ()
testCaseDesugaring = do
    let inputSource = unlines
          [ "module CaseDesugaring where"
          , "f :: Bool -> ()"
          , "f x = case x of"
          , "        True -> ()"
          ]

        -- Expected desugaring:
        --
        -- CaseDesugaring.f
        --      = \ (x :: GHC.Types.Bool) ->
        --          case x of {
        --            __DEFAULT ->
        --              case Control.Exception.Base.patError ...
        --              of {
        --              };
        --            GHC.Types.True -> GHC.Tuple.()
        --          }
        --
        isExpectedDesugaring p = case findExpr "f" p of
          Just e0
            | Lam x (untick -> Case (Var x') _ _ [alt0, _alt1]) <- e0
            , x == x'
            , Alt DEFAULT [] e1 <- alt0
            , Case e2 _ _ [] <- e1
            , (Var e3,_) <- GHC.collectArgs e2
            -> e3 == pAT_ERROR_ID
          _ -> False

    coreProgram <- compileToCore "CaseDesugaring" inputSource
    unless (isExpectedDesugaring coreProgram) $
      fail $ unlines $
        "Unexpected desugaring:" : map showPprQualified coreProgram

-- | Tests that numeric literal expressions desugar as Liquid Haskell expects.
--
-- https://github.com/ucsd-progsys/liquidhaskell/issues/2237
testNumLitDesugaring :: IO ()
testNumLitDesugaring = do
    let inputSource = unlines
          [ "module NumLitDesugaring where"
          , "f :: Num a => a"
          , "f = 1"
          ]

        -- Expected desugaring:
        --
        -- NumLitDesugaring.f
        --      = \@a dict -> fromInteger @a dict (GHC.Num.Integer.IS 1#)
        --
        isExpectedDesugaring p = case findExpr "f" p of
          Just e0
            | Lam _a (Lam _dict (untick . dropLets -> App fromIntegerApp (App (Var vIS) lit))) <- e0
            , App (App (Var vFromInteger) _aty) _numDict <- fromIntegerApp
            , GHC.idName vFromInteger  == GHC.fromIntegerName
            , GHC.nameStableString (GHC.idName vIS) == GHC.nameStableString GHC.integerISDataConName
            , Lit (LitNumber LitNumInt 1) <- lit
            -> True
          _ -> False

    coreProgram <- compileToCore "NumLitDesugaring" inputSource
    unless (isExpectedDesugaring coreProgram) $
      fail $ unlines $
        "Unexpected desugaring:" : map showPprQualified coreProgram

dropLets :: GHC.CoreExpr -> GHC.CoreExpr
dropLets (Let _ e) = dropLets e
dropLets e         = e

-- | Tests that dollar sign desugars as Liquid Haskell expects.
testDollarDesugaring :: IO ()
testDollarDesugaring = do
    let inputSource = unlines
          [ "module DollarDesugaring where"
          , "f :: ()"
          , "f = (\\_ -> ()) $ 'a'"
          ]

        isExpectedDesugaring p = case findExpr "f" p of
          Just e0
            | Just (Lam _ _, App _ (Lit (LitChar 'a'))) <- splitDollarApp e0
            -> True
          _ -> False

    coreProgram <- compileToCore "DollarDesugaring" inputSource
    unless (isExpectedDesugaring coreProgram) $
      fail $ unlines $
        "Unexpected desugaring:" : map showPprQualified coreProgram

-- | Find the Core expression bound to the given name.
findExpr :: String -> GHC.CoreProgram -> Maybe GHC.CoreExpr
findExpr _ [] =
  Nothing
findExpr name (p:ps) = case p of
  GHC.NonRec b e
    | occNameString (GHC.occName b) == name
    -> Just e
  GHC.Rec binds
    | Just (_, e) <- find (\(b, _e) -> occNameString (GHC.occName b) == name) binds
    -> Just e
  _ -> findExpr name ps


compileToCore :: String -> String -> IO [GHC.CoreBind]
compileToCore modName inputSource = do
    GHC.runGhc (Just libdir) $ do
      (_, tcMod) <- typecheckSourceCode modName inputSource
      dsMod <- GHC.desugarModule tcMod
      return $ GHC.mg_binds $ GHC.dm_core_module dsMod

typecheckSourceCode
  :: GHC.GhcMonad m => String -> String -> m (GHC.ModSummary, GHC.TypecheckedModule)
typecheckSourceCode modName inputSource = do
    now <- liftIO getCurrentTime
    df1 <- GHC.getSessionDynFlags
    GHC.setSessionDynFlags $ df1 { GHC.backend = GHC.bytecodeBackend }
    let target = GHC.Target
               { GHC.targetId           = GHC.TargetFile (modName ++ ".hs") Nothing
               , GHC.targetUnitId       = GHC.homeUnitId_ df1
               , GHC.targetAllowObjCode = False
               , GHC.targetContents     = Just (GHC.stringToStringBuffer inputSource, now)
               }
    GHC.setTargets [target]
    void $ GHC.depanal [] False

    ms <- GHC.getModSummary
            (GHC.mkModule GHC.mainUnit (GHC.mkModuleName modName))
    tm <- GHC.parseModule ms >>= GHC.typecheckModule
    return (ms, tm)

-- | Like 'compileToCore' but applies 'addNoInlinePragmasToBinds' before
-- desugaring, simulating what LH's plugin does to preserve bindings that
-- would otherwise be inlined away.
compileToCoreWithLH :: String -> String -> IO [GHC.CoreBind]
compileToCoreWithLH modName inputSource = do
    GHC.runGhc (Just libdir) $ do
      (ms, tcMod) <- typecheckSourceCode modName inputSource
      let (tcg, _) = GHC.tm_internals_ tcMod
          tcg' = addNoInlinePragmasToBinds tcg
      hsc_env <- GHC.getSession
      guts <- liftIO $ GHC.hscDesugar hsc_env ms tcg'
      return $ GHC.mg_binds guts

-- | Tests that dead bindings (unused where-clause bindings) are preserved
-- when 'addNoInlinePragmasToBinds' marks Ids as exported.
testDeadBindingPreservation :: IO ()
testDeadBindingPreservation = do
    let inputSource = unlines
          [ "module DeadBindingPreservation where"
          , "f :: Int -> ()"
          , "f x = ()"
          , "  where"
          , "    z = x + 1"
          ]

        -- The dead binding 'z' should still appear in the Core output.
        hasDeadBinding p = case findExpr "f" p of
          Just e -> hasLetNamed "z" e
          _      -> False

    coreProgram <- compileToCoreWithLH "DeadBindingPreservation" inputSource
    unless (hasDeadBinding coreProgram) $
      fail $ unlines $
        "Dead binding 'z' was eliminated:" : map showPprQualified coreProgram

-- | Tests that a binding marked as exported is not inlined even when it
-- occurs exactly once (i.e. it would normally be inlined by the simple
-- optimizer).
testExportedBindingNotInlined :: IO ()
testExportedBindingNotInlined = do
    let inputSource = unlines
          [ "module ExportedBindingNotInlined where"
          , "f :: Int -> Int"
          , "f x = z"
          , "  where"
          , "    z = x + 1"
          ]

        -- The binding 'z' is used exactly once. Without the exported
        -- marking, the simple optimizer would inline it. With it,
        -- 'z' should still appear as a let-binding.
        hasBinding p = case findExpr "f" p of
          Just e -> hasLetNamed "z" e
          _      -> False

    coreProgram <- compileToCoreWithLH "ExportedBindingNotInlined" inputSource
    unless (hasBinding coreProgram) $
      fail $ unlines $
        "Binding 'z' was inlined:" : map showPprQualified coreProgram

-- | Check if an expression contains a let-binding with the given name.
hasLetNamed :: String -> GHC.CoreExpr -> Bool
hasLetNamed name = go
  where
    go (Let (GHC.NonRec b _) body) =
      occNameString (GHC.occName b) == name || go body
    go (Let (GHC.Rec pairs) body) =
      any (\(b, _) -> occNameString (GHC.occName b) == name) pairs || go body
    go (Lam _ e) = go e
    go (App e1 e2) = go e1 || go e2
    go (GHC.Case _ _ _ alts) = any (\(Alt _ _ rhs) -> go rhs) alts
    go (GHC.Cast e _) = go e
    go (GHC.Tick _ e) = go e
    go _ = False
