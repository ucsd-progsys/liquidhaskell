{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
module Language.Haskell.Liquid.Model where

import Control.Monad
import Control.Monad.IO.Class
import qualified Data.HashMap.Strict as HM
import Data.Maybe
import GHC.Prim
import Unsafe.Coerce

import Language.Fixpoint.Types (FixResult(..), Symbol, symbol, Sort(..), Expr(..))
import Language.Haskell.Liquid.GHC.Interface
import Language.Haskell.Liquid.Types hiding (var)
import Language.Haskell.Liquid.Types.RefType
import Test.Target.Expr
import Test.Target.Monad
import Test.Target.Targetable hiding (query)
import Test.Target.Util

import GHC
import InstEnv
import Type
import TysWiredIn

import Debug.Trace

getModels :: GhcInfo -> Config -> FixResult Cinfo -> IO (FixResult Cinfo)
getModels info cfg fi = case fi of
  Unsafe cs -> fmap Unsafe . runLiquidGhc (Just (env info)) cfg $ do
    imps <- getContext
    setContext (IIDecl ((simpleImportDecl (mkModuleName "Test.Target.Targetable"))
                                          { ideclQualified = True })
                : imps)
    mapM (getModel cfg) cs
  _         -> return fi

getModel :: Config -> Cinfo -> Ghc Cinfo
getModel cfg ci@(Ci { ci_err = Just err@(ErrSubType { ctx, tact, texp }) }) = do
  let vts = HM.toList ctx
  liftIO $ print $ length vts
  vtds <- makeQueries vts
  liftIO $ print $ length vtds

  let model = mempty
  return (ci { ci_err = Just (err { model = model })})

getModel _ ci = return ci


data Dict :: Constraint -> * where
  Dict :: a => Dict a

data TargetDict = forall t. TargetDict (Dict (Targetable t))

makeQueries :: [(Symbol, SpecType)] -> Ghc [(Symbol, SpecType, TargetDict)]
makeQueries bnds = catMaybes <$> mapM addDict bnds

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
          hv <- compileExpr $ traceShowId
                ("Language.Haskell.Liquid.Model.Dict :: Language.Haskell.Liquid.Model.Dict (Test.Target.Targetable.Targetable ("++ showpp mt ++"))")
          let d = TargetDict $ unsafeCoerce hv
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
