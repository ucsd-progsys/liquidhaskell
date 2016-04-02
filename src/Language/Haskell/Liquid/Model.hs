{-# LANGUAGE NamedFieldPuns #-}
module Language.Haskell.Liquid.Model where

import Language.Fixpoint.Types (FixResult(..), Symbol, symbol, Sort(..), Expr(..))
import Language.Haskell.Liquid.Types hiding (var)
import Language.Haskell.Liquid.Types.RefType
import Test.Target.Expr
import Test.Target.Monad
import Test.Target.Targetable hiding (query)
import Test.Target.Util

-- import Debug.Trace

getModels :: Config -> FixResult Cinfo -> IO (FixResult Cinfo)
getModels cfg fi = case fi of
  Unsafe cs -> Unsafe <$> mapM (getModel cfg) cs
  _         -> return fi

getModel :: Config -> Cinfo -> IO Cinfo
getModel cfg ci@(Ci { ci_err = Just err@(ErrSubType { ctx, tact, texp }) }) = do
  let model = mempty
  return (ci { ci_err = Just (err { model = model })})

getModel _ ci = return ci


query :: Int -> SpecType -> Target Symbol
query d t = {- inModule mod . -} making sort $ do
    xs <- queryCtors d t
    x  <- fresh sort
    oneOf x xs
    constrain $ ofReft (reft t) (var x)
    return x
   where
     -- mod  = symbol $ GHC.Generics.moduleName (undefined :: D1 c f a)
     sort = FObj . symbol . showpp $ toType t

queryCtors :: Int -> SpecType -> Target [(Expr, Expr)]
queryCtors d t = undefined
