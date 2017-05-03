{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Bare.Expand ( ExpandAliases (..) ) where

import           Prelude                          hiding (error)
import           Control.Monad.State              hiding (forM)
import qualified Data.HashMap.Strict              as M
import           Language.Fixpoint.Types          (Expr(..), Reft(..), mkSubst, subst, eApps, splitEApp, Symbol, Subable)
-- import qualified Language.Fixpoint.Types as F 
import           Language.Haskell.Liquid.Misc     (firstMaybes, safeZipWithError)
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Bare.Env

class ExpandAliases a where
  expand :: a -> BareM a

instance ExpandAliases Expr where
  expand = expandExpr

instance ExpandAliases Reft where
  expand = txPredReft' expandExpr

instance ExpandAliases SpecType where
  expand = mapReftM expand

instance ExpandAliases Body where
  expand (E e)   = E   <$> expand e
  expand (P e)   = P   <$> expand e
  expand (R x e) = R x <$> expand e

instance ExpandAliases ty => ExpandAliases (Def ty ctor) where
  expand (Def f xts c t bxts b) =
    Def f <$> expand xts
          <*> pure c
          <*> expand t
          <*> expand bxts
          <*> expand b

instance ExpandAliases ty => ExpandAliases (Measure ty ctor) where
  expand (M n t ds) =
    M n <$> expand t <*> expand ds

instance ExpandAliases DataConP where
  expand d = do
    tyRes'    <- expand $ tyRes    d
    tyConsts' <- expand $ tyConsts d
    tyArgs'   <- expand $ tyArgs   d
    return d { tyRes = tyRes', tyConsts = tyConsts', tyArgs = tyArgs' }

instance ExpandAliases RReft where
  expand = mapM expand

instance (ExpandAliases a) => ExpandAliases (Located a) where
  expand = mapM expand

instance (ExpandAliases a) => ExpandAliases (Maybe a) where
  expand = mapM expand

instance (ExpandAliases a) => ExpandAliases [a] where
  expand = mapM expand

instance (ExpandAliases b) => ExpandAliases (a, b) where
  expand = mapM expand

--------------------------------------------------------------------------------
-- Expand Reft Preds & Exprs ---------------------------------------------------
--------------------------------------------------------------------------------
txPredReft' :: (Expr -> BareM Expr) -> Reft -> BareM Reft
txPredReft' f (Reft (v, ra)) = Reft . (v,) <$> f ra

--------------------------------------------------------------------------------
-- Expand Exprs ----------------------------------------------------------------
--------------------------------------------------------------------------------
expandExpr :: Expr -> BareM Expr
expandExpr = go
  where
    go e@(EApp _ _)    = {- tracepp ("EXPANDEAPP e = " ++ showpp e ) <$> -} expandEApp (splitEApp e)
    go (EVar x)        = expandSym x
    go (ENeg e)        = ENeg        <$> go e
    go (ECst e s)      = (`ECst` s)  <$> go e
    go (PAnd ps)       = PAnd        <$> mapM go ps
    go (POr ps)        = POr         <$> mapM go ps
    go (PNot p)        = PNot        <$> go p
    go (PAll xs p)     = PAll xs     <$> go p
    go (PExist s e)    = PExist s    <$> go e
    go (ELam xt e)     = ELam xt     <$> go e
    go (ETApp e s)     = (`ETApp` s) <$> go e
    go (ETAbs e s)     = (`ETAbs` s) <$> go e
    go (EBin op e1 e2) = EBin op     <$> go e1  <*> go e2
    go (PImp p q)      = PImp        <$> go p   <*> go q
    go (PIff p q)      = PIff        <$> go p   <*> go q
    go (PAtom b e e')  = PAtom b     <$> go e   <*> go e'
    go (EIte p e1 e2)  = EIte        <$> go p   <*> go e1 <*> go e2
    -- go e@(EVar _)      = return e
    go e@(PKVar _ _)   = return e
    go (PGrad k su e)  = PGrad k su <$> go e
    go e@(ESym _)      = return e
    go e@(ECon _)      = return e

expandSym :: Symbol -> BareM Expr
expandSym s = do
  s' <- expandSym' s
  expandEApp (EVar s', [])

expandSym' :: Symbol -> BareM Symbol
expandSym' s = do
  axs <- gets axSyms
  let s' = dropModuleNamesAndUnique s
  return $ if M.member s' axs then s' else s

expandEApp :: (Expr, [Expr]) -> BareM Expr
expandEApp (EVar f, es) = do
  eAs   <- gets (exprAliases . rtEnv)
  let mBody = firstMaybes [M.lookup f eAs, M.lookup (dropModuleUnique f) eAs]
  case mBody of
    Just re -> expandApp re   <$> mapM expandExpr es
    Nothing -> eApps (EVar f) <$> mapM expandExpr es
expandEApp (f, es) =
  return $ eApps f es

--------------------------------------------------------------------------------
-- | Expand Alias Application --------------------------------------------------
--------------------------------------------------------------------------------
expandApp :: Subable ty => RTAlias Symbol ty -> [Expr] -> ty
expandApp re es = subst su $ rtBody re
  where
    su          = mkSubst $ safeZipWithError msg (rtVArgs re) es
    msg         = "Malformed alias application" ++ "\n\t"
               ++ show (rtName re)
               ++ " defined at " ++ show (rtPos re)
               ++ "\n\texpects " ++ show (length $ rtVArgs re)
               ++ " arguments but it is given " ++ show (length es)
