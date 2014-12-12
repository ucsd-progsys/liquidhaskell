{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bare.Reft (
    expandReft

  , expandPred
  , expandExpr
  ) where

import Control.Applicative ((<$>), (<*>))
import Control.Monad.Reader hiding (forM)
import Control.Monad.State hiding (forM)
import Text.Parsec.Pos

import qualified Data.HashMap.Strict as M

import Language.Fixpoint.Misc (errorstar)
import Language.Fixpoint.Types (Expr(..), Pred(..), Refa(..), Reft(..), Symbol, mkSubst, subst)

import Language.Haskell.Liquid.Misc (safeZipWithError)
import Language.Haskell.Liquid.Types

import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Bare.Resolve

--------------------------------------------------------------------------------
-- Expand Reft Preds & Exprs ---------------------------------------------------
--------------------------------------------------------------------------------

-- TOOD: Add type signature
expandReft l = txPredReft (expandPred l) (expandExpr l)

txPredReft :: (Pred -> BareM Pred) -> (Expr -> BareM Expr) -> RReft -> BareM RReft
txPredReft f fe (U r p l) = (\r -> U r p l) <$> txPredReft' f r
  where 
    txPredReft' f (Reft (v, ras)) = Reft . (v,) <$> mapM (txPredRefa f) ras
    txPredRefa  f (RConc p)       = fmap RConc $ (f <=< mapPredM fe) p
    txPredRefa  _ z               = return z

mapPredM f = go
  where
    go (PAnd ps)       = PAnd <$> mapM go ps
    go (POr ps)        = POr  <$> mapM go ps
    go (PNot p)        = PNot <$> go p
    go (PImp p q)      = PImp <$> go p <*> go q
    go (PIff p q)      = PIff <$> go p <*> go q
    go (PBexp e)       = PBexp <$> f e
    go (PAtom b e1 e2) = PAtom b <$> f e1 <*> f e2
    go (PAll xs p)     = PAll xs <$> go p
    go p               = return p

--------------------------------------------------------------------------------
-- Expand Preds ----------------------------------------------------------------
--------------------------------------------------------------------------------

expandPred l = expandPred' l []

expandPred' :: SourcePos -> [Symbol] -> Pred -> BareM Pred
expandPred' l = go
  where 
    go s (PBexp (EApp f@(Loc l' f') es))
      | f' `elem` s
        = errorstar $ "Cyclic Predicate Alias: " ++ show (f':s)
      | otherwise = do
          env <- gets (predAliases.rtEnv)
          case M.lookup f' env of
            Just (Left (mod,rp)) -> do
              body <- inModule mod $ withVArgs l' (rtVArgs rp) $ expandPred' l' (f':s) $ rtBody rp
              let rp' = rp { rtBody = body }
              setRPAlias f' $ Right $ rp'
              expandEApp l (f':s) rp' <$> resolve l es
            Just (Right rp) ->
              withVArgs l (rtVArgs rp) (expandEApp l (f':s) rp <$> resolve l es)
            Nothing -> fmap PBexp (EApp <$> resolve l f <*> resolve l es)
    go s (PAnd ps)                = PAnd <$> (mapM (go s) ps)
    go s (POr  ps)                = POr  <$> (mapM (go s) ps)
    go s (PNot p)                 = PNot <$> (go s p)
    go s (PImp p q)               = PImp <$> (go s p) <*> (go s q)
    go s (PIff p q)               = PIff <$> (go s p) <*> (go s q)
    go s (PAll xts p)             = PAll xts <$> (go s p)
    go _ p                        = resolve l p

--------------------------------------------------------------------------------
-- Expand Exprs ----------------------------------------------------------------
--------------------------------------------------------------------------------

expandExpr l = expandExpr' l []

expandExpr' :: SourcePos -> [Symbol] -> Expr -> BareM Expr
expandExpr' l = go
  where 
    --NOTE: don't do any name-resolution here, expandPAlias runs afterwards and
    --      will handle it
    go s (EApp f@(Loc l' f') es)
      | f' `elem` s
        = errorstar $ "Cyclic Predicate Alias: " ++ show (f':s)
      | otherwise = do
          env <- gets (exprAliases.rtEnv)
          case M.lookup f' env of
            Just (Left (mod,re)) -> do
              body <- inModule mod $ withVArgs l' (rtVArgs re) $ expandExpr' l' (f':s) $ rtBody re
              let re' = re { rtBody = body }
              setREAlias f' $ Right $ re'
              expandEApp l (f':s) re' <$> mapM (go (f':s)) es
            Just (Right re) ->
              withVArgs l (rtVArgs re) (expandEApp l (f':s) re <$> mapM (go (f':s)) es)
            Nothing -> EApp f <$> mapM (go s) es
    go s (EBin op e1 e2)          = EBin op <$> go s e1 <*> go s e2
    go s (EIte p  e1 e2)          = EIte p  <$> go s e1 <*> go s e2
    go s (ECst e st)              = (`ECst` st) <$> go s e
    go _ e                        = return e

-- FIXME: `_` isn't used here. Should it be?
expandEApp l _ re es
  = subst su $ rtBody re
  where su  = mkSubst $ safeZipWithError msg (rtVArgs re) es
        msg = "Malformed alias application at " ++ show l ++ "\n\t"
               ++ show (rtName re) 
               ++ " defined at " ++ show (rtPos re)
               ++ "\n\texpects " ++ show (length $ rtVArgs re)
               ++ " arguments but it is given " ++ show (length es)

