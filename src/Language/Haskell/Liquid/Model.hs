{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
module Language.Haskell.Liquid.Model where

import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import           Control.Monad.State
import qualified Data.HashMap.Strict                   as HM
import           Data.Maybe
import           Data.Proxy
import           Data.Typeable
import           GHC.Prim
import           Text.PrettyPrint.HughesPJ
import           Unsafe.Coerce

import           Language.Fixpoint.Types               (FixResult(..), Symbol, symbol, Sort(..), Expr(..))
import           Language.Fixpoint.Smt.Interface
import           Language.Haskell.Liquid.GHC.Interface
import           Language.Haskell.Liquid.Types         hiding (var)
import           Language.Haskell.Liquid.Types.RefType
import           Test.Target.Expr
import           Test.Target.Monad
import           Test.Target.Targetable
import           Test.Target.Testable
import           Test.Target.Util

import           GHC
import           InstEnv
import           Type
import           TysWiredIn

import           Debug.Trace

getModels :: GhcInfo -> Config -> FixResult Cinfo -> IO (FixResult Cinfo)
getModels info cfg fi = case fi of
  Unsafe cs -> fmap Unsafe . runLiquidGhc (Just (env info)) cfg $ do
    imps <- getContext
    setContext (IIDecl ((simpleImportDecl (mkModuleName "Test.Target.Targetable"))
                                          { ideclQualified = True })
                : imps)
    mapM (getModel info cfg) cs
  _         -> return fi

getModel :: GhcInfo -> Config -> Cinfo -> Ghc Cinfo
getModel info cfg ci@(Ci { ci_err = Just err@(ErrSubType { ctx, tact, texp }) }) = do
  let vts = HM.toList ctx
  liftIO $ print $ length vts
  vtds <- addDicts vts
  liftIO $ print $ length vtds

  let opts = defaultOpts
  smt <- liftIO $ makeContext False (solver opts) (target info)
  model <- liftIO $ runTarget opts (initState "" (spec info) smt) $ do
    cs <- gets ctorEnv
    traceShowM ("constructors", cs)
    n <- asks depth
    vs <- forM vtds $ \(v, t, TargetDict d@Dict) -> query (dictProxy d) n t
    traceM "DONE QUERY"
    setup
    traceM "DONE SETUP"
    _ <- liftIO $ command smt CheckSat
    traceM "DONE CHECKSAT"
    forM (zip vs vtds) $ \(sv, (v, t, TargetDict d@Dict)) -> do
      x <- decode sv t
      return (v, text (show (toExpr (x `asTypeOfDict` d))))
  traceM "DONE DECODE"
  traceShowM model
  -- let model = mempty

  _ <- liftIO $ cleanupContext smt
  return (ci { ci_err = Just (err { model = HM.fromList model })})

getModel _ _ ci = return ci

dictProxy :: forall t. Dict (Targetable t) -> Proxy t
dictProxy Dict = Proxy

asTypeOfDict :: forall t. t -> Dict (Targetable t) -> t
x `asTypeOfDict` Dict = x

data Dict :: Constraint -> * where
  Dict :: a => Dict a
  deriving Typeable

data TargetDict = forall t. TargetDict (Dict (Targetable t))

addDicts :: [(Symbol, SpecType)] -> Ghc [(Symbol, SpecType, TargetDict)]
addDicts bnds = catMaybes <$> mapM addDict bnds

addDict :: (Symbol, SpecType) -> Ghc (Maybe (Symbol, SpecType, TargetDict))
addDict (v, t) =
  case tyConAppTyCon_maybe (toType t) of
    Nothing -> return Nothing
    Just tc -> do
      getInfo False (getName tc) >>= \case
        Nothing -> return Nothing
        Just (_, _, cis, _) -> do
          let mt = monomorphize (toType t)
          unless ("Test.Target.Targetable.Targetable"
                  `elem` map (showpp.is_cls_nm) cis) $
            void $ runDecls $ traceShowId
                   ("instance Test.Target.Targetable.Targetable ("
                    ++ showpp mt ++ ")")
          -- FIXME: HOW THE HELL DOES THIS BREAK THE PRINTER??!?!??!?!
          hv <- compileExpr $ traceShowId
                ("Language.Haskell.Liquid.Model.Dict :: Language.Haskell.Liquid.Model.Dict (Test.Target.Targetable.Targetable ("++ showpp mt ++"))")
          let d = TargetDict $ unsafeCoerce hv
          -- let d = TargetDict (Dict :: Dict (Targetable [Int]))
          return (Just (v, t, d))


monomorphize :: Type -> Type
monomorphize t = substTyWith tvs (replicate (length tvs) intTy) t
  where
  tvs = varSetElemsKvsFirst (tyVarsOfType t)

-- query :: Int -> SpecType -> Target Symbol
-- query d t = {- inModule mod . -} making sort $ do
--     xs <- queryCtors d t
--     x  <- fresh sort
--     oneOf x xs
--     constrain $ ofReft (reft t) (var x)
--     return x
--    where
--      -- mod  = symbol $ GHC.Generics.moduleName (undefined :: D1 c f a)
--      sort = FObj . symbol . showpp $ toType t

-- queryCtors :: Int -> SpecType -> Target [(Expr, Expr)]
-- queryCtors d t = undefined
