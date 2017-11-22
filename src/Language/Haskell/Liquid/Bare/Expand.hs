{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Bare.Expand (
  -- * Alias Expansion
  ExpandAliases (..)
  ) where

import           Prelude                          hiding (error)
import           Control.Monad.State              hiding (forM)
import qualified Data.HashMap.Strict              as M
import qualified Language.Fixpoint.Types          as F
import           Language.Fixpoint.Types          (Expr(..), Reft(..), mkSubst, subst, eApps, splitEApp, Symbol, Subable)
import           Language.Haskell.Liquid.Misc     (firstMaybes, safeZipWithError)
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Bare.Env

class ExpandAliases a where
  expand :: F.SrcSpan -> a -> BareM a

instance ExpandAliases Expr where
  expand = expandExpr

instance ExpandAliases Reft where
  expand = txPredReft' expandExpr

instance ExpandAliases SpecType where
  expand z = mapReftM (expand z)

instance ExpandAliases Body where
  expand z (E e)   = E   <$> expand z e
  expand z (P e)   = P   <$> expand z e
  expand z (R x e) = R x <$> expand z e

instance ExpandAliases ty => ExpandAliases (Def ty ctor) where
  expand z (Def f xts c t bxts b) =
    Def f <$> expand z xts
          <*> pure c
          <*> expand z t
          <*> expand z bxts
          <*> expand z b

instance ExpandAliases ty => ExpandAliases (Measure ty ctor) where
  expand z (M n t ds) =
    M n <$> expand z t <*> expand z ds

instance ExpandAliases DataConP where
  expand z d = do
    tyRes'    <- expand z (tyRes     d)
    tyConsts' <- expand z (tyConstrs d)
    tyArgs'   <- expand z (tyArgs    d)
    return d { tyRes =  tyRes', tyConstrs = tyConsts', tyArgs = tyArgs' }

instance ExpandAliases RReft where
  expand z = mapM (expand z)

instance (ExpandAliases a) => ExpandAliases (Located a) where
  expand z = mapM (expand z)

instance (ExpandAliases a) => ExpandAliases (Maybe a) where
  expand z = mapM (expand z)

instance (ExpandAliases a) => ExpandAliases [a] where
  expand z = mapM (expand z)

instance (ExpandAliases b) => ExpandAliases (a, b) where
  expand z = mapM (expand z)

--------------------------------------------------------------------------------
-- Expand Reft Preds & Exprs ---------------------------------------------------
--------------------------------------------------------------------------------
txPredReft' :: (a -> Expr -> BareM Expr) -> a -> Reft -> BareM Reft
txPredReft' f z (Reft (v, ra)) = Reft . (v,) <$> f z ra

--------------------------------------------------------------------------------
-- Expand Exprs ----------------------------------------------------------------
--------------------------------------------------------------------------------
expandExpr :: F.SrcSpan -> Expr -> BareM Expr
expandExpr sp = go
  where
    go e@(EApp _ _)    = {- tracepp ("EXPANDEAPP e = " ++ showpp e ) <$> -} expandEApp sp (splitEApp e)
    go (EVar x)        = expandSym sp x
    go (ENeg e)        = ENeg        <$> go e
    go (ECst e s)      = (`ECst` s)  <$> go e
    go (PAnd ps)       = PAnd        <$> mapM go ps
    go (POr ps)        = POr         <$> mapM go ps
    go (PNot p)        = PNot        <$> go p
    go (PAll xs p)     = PAll xs     <$> go p
    go (PExist s e)    = PExist s    <$> go e
    go (ELam xt e)     = ELam xt     <$> go e
    go (ECoerc a t e)  = ECoerc a t  <$> go e
    go (ETApp e s)     = (`ETApp` s) <$> go e
    go (ETAbs e s)     = (`ETAbs` s) <$> go e
    go (EBin op e1 e2) = EBin op     <$> go e1  <*> go e2
    go (PImp p q)      = PImp        <$> go p   <*> go q
    go (PIff p q)      = PIff        <$> go p   <*> go q
    go (PAtom b e e')  = PAtom b     <$> go e   <*> go e'
    go (EIte p e1 e2)  = EIte        <$> go p   <*> go e1 <*> go e2
    -- go e@(EVar _)      = return e
    go e@(PKVar _ _)   = return e
    go (PGrad k su i e)  = PGrad k su i <$> go e
    go e@(ESym _)      = return e
    go e@(ECon _)      = return e

expandSym :: F.SrcSpan -> Symbol -> BareM Expr
expandSym sp s = do
  s' <- expandSym' sp s
  expandEApp sp (EVar s', [])

expandSym' :: F.SrcSpan -> Symbol -> BareM Symbol
expandSym' sp s = do
  axs <- gets axSyms
  let s' = dropModuleNamesAndUnique s
  return $ if M.member s' axs then {- tracepp "EXPANDSYM" -} s' else s

expandEApp :: F.SrcSpan -> (Expr, [Expr]) -> BareM Expr
expandEApp sp (EVar f, es) = do
  eAs   <- gets (exprAliases . rtEnv)
  let mBody = firstMaybes [M.lookup f eAs, M.lookup (dropModuleUnique f) eAs]
  case mBody of
    Just re -> expandApp sp re <$> mapM (expandExpr sp) es
    Nothing -> eApps (EVar f)  <$> mapM (expandExpr sp) es
expandEApp s (f, es) =
  return $ eApps f es

--------------------------------------------------------------------------------
-- | Expand Alias Application --------------------------------------------------
--------------------------------------------------------------------------------
expandApp :: Subable ty => F.SrcSpan -> RTAlias Symbol ty -> [Expr] -> ty
expandApp sp re es = subst su $ rtBody re
  where
    su             = mkSubst $ safeZipWithError msg (rtVArgs re) es
    msg            = "Malformed alias application" ++ "\n\t"
                  ++ show (rtName re)
                  ++ " defined at " ++ show (rtPos re)
                  ++ "\n\texpects " ++ show (length $ rtVArgs re)
                  ++ " arguments but it is given " ++ show (length es)
