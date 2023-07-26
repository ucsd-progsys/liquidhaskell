{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Language.Haskell.Liquid.Constraint.Template (
  Template(..)
, unTemplate
, varTemplate
, addPostTemplate
, safeFromAsserted
, topSpecType
, derivedVar
, extender
) where

import           Prelude hiding (error)
import qualified Data.Foldable                                 as F
import qualified Data.Traversable                              as T
import qualified Data.HashSet                                  as S
import           Control.Monad.State ( gets )
import           Text.PrettyPrint.HughesPJ ( text, (<+>) )
import           GHC.Types.Var (Var)
import           GHC.Core (CoreExpr)
import           GHC.Core.Utils ( exprType )
import qualified Language.Fixpoint.Types                       as F
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Env ( lookupREnv, (+=) )
import           Language.Haskell.Liquid.Constraint.Monad (addPost, addW)
import           Language.Haskell.Liquid.Constraint.Fresh (refreshArgsTop, freshTyExpr)

-- Template

data Template a
  = Asserted a
  | Assumed a
  | Internal a
  | Unknown
  deriving (Functor, F.Foldable, T.Traversable)

deriving instance (Show a) => (Show (Template a))

instance PPrint a => PPrint (Template a) where
  pprintTidy k (Asserted t) = text "Asserted" <+> pprintTidy k t
  pprintTidy k (Assumed  t) = text "Assumed"  <+> pprintTidy k t
  pprintTidy k (Internal t) = text "Internal" <+> pprintTidy k t
  pprintTidy _ Unknown      = text "Unknown"

unTemplate :: Template t -> t
unTemplate (Asserted t) = t
unTemplate (Assumed t)  = t
unTemplate (Internal t) = t
unTemplate _            = panic Nothing "Constraint.Template.unTemplate called on `Unknown`"

addPostTemplate :: CGEnv
                -> Template SpecType
                -> CG (Template SpecType)
addPostTemplate γ (Asserted t) = Asserted <$> addPost γ t
addPostTemplate γ (Assumed  t) = Assumed  <$> addPost γ t
addPostTemplate γ (Internal t) = Internal <$> addPost γ t
addPostTemplate _ Unknown      = return Unknown

safeFromAsserted :: [Char] -> Template t -> t
safeFromAsserted _   (Asserted t) = t
safeFromAsserted msg  _           = panic Nothing $ "safeFromAsserted:" ++ msg

-- | @varTemplate@ is only called with a `Just e` argument when the `e`
-- corresponds to the body of a @Rec@ binder.
varTemplate :: CGEnv -> (Var, Maybe CoreExpr) -> CG (Template SpecType)
varTemplate γ (x, eo) = varTemplate' γ (x, eo) >>= mapM (topSpecType x)

-- | @lazVarTemplate@ is like `varTemplate` but for binders that are *not*
--   termination checked and hence, the top-level refinement / KVar is
--   stripped out. e.g. see tests/neg/T743.hs
-- varTemplate :: CGEnv -> (Var, Maybe CoreExpr) -> CG (Template SpecType)
-- lazyVarTemplate γ (x, eo) = dbg <$> (topRTypeBase <$>) <$> varTemplate' γ (x, eo)
--   where
--    dbg   = traceShow ("LAZYVAR-TEMPLATE: " ++ show x)

varTemplate' :: CGEnv -> (Var, Maybe CoreExpr) -> CG (Template SpecType)
varTemplate' γ (x, eo)
  = case (eo, lookupREnv (F.symbol x) (grtys γ), lookupREnv (F.symbol x) (assms γ), lookupREnv (F.symbol x) (intys γ)) of
      (_, Just t, _, _) -> Asserted <$> refreshArgsTop (x, t)
      (_, _, _, Just t) -> Internal <$> refreshArgsTop (x, t)
      (_, _, Just t, _) -> Assumed  <$> refreshArgsTop (x, t)
      (Just e, _, _, _) -> do t <- freshTyExpr (typeclass (getConfig γ)) (RecBindE x) e (exprType e)
                              addW (WfC γ t)
                              Asserted <$> refreshArgsTop (x, t)
      (_,      _, _, _) -> return Unknown

-- | @topSpecType@ strips out the top-level refinement of "derived var"
topSpecType :: Var -> SpecType -> CG SpecType
topSpecType x t = do
  info <- gets ghcI
  return $ if derivedVar (giSrc info) x then topRTypeBase t else t

derivedVar :: TargetSrc -> Var -> Bool
derivedVar src x = S.member x (giDerVars src)

extender :: F.Symbolic a => CGEnv -> (a, Template SpecType) -> CG CGEnv
extender γ (x, Asserted t)
  = case lookupREnv (F.symbol x) (assms γ) of
      Just t' -> γ += ("extender", F.symbol x, t')
      _       -> γ += ("extender", F.symbol x, t)
extender γ (x, Assumed t)
  = γ += ("extender", F.symbol x, t)
extender γ _
  = return γ
