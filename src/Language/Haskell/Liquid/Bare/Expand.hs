{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bare.Expand (
    expandReft
  , expandPred
  , expandExpr
  ) where

import Control.Applicative ((<$>), (<*>))
import Control.Monad.Reader hiding (forM)
import Control.Monad.State hiding (forM)

import qualified Data.HashMap.Strict as M

import Language.Fixpoint.Types (Expr(..), Pred(..), Refa(..), Reft(..), mkSubst, subst)

import Language.Haskell.Liquid.Misc (safeZipWithError)
import Language.Haskell.Liquid.Types

import Language.Haskell.Liquid.Bare.Env

--------------------------------------------------------------------------------
-- Expand Reft Preds & Exprs ---------------------------------------------------
--------------------------------------------------------------------------------

-- TOOD: Add type signature
expandReft = txPredReft expandPred expandExpr

txPredReft :: (Pred -> BareM Pred) -> (Expr -> BareM Expr) -> RReft -> BareM RReft
txPredReft f fe (U r p l) = (\r -> U r p l) <$> txPredReft' f r
  where 
    txPredReft' f (Reft (v, ras)) = Reft . (v,) <$> mapM (txPredRefa f) ras
    txPredRefa  f (RConc p)       = fmap RConc $ (f <=< mapPredM fe) p
    txPredRefa  _ z               = return z

mapPredM f = go
  where
    go PTrue           = return PTrue
    go PFalse          = return PFalse
    go (PAnd ps)       = PAnd <$> mapM go ps
    go (POr ps)        = POr  <$> mapM go ps
    go (PNot p)        = PNot <$> go p
    go (PImp p q)      = PImp <$> go p <*> go q
    go (PIff p q)      = PIff <$> go p <*> go q
    go (PBexp e)       = PBexp <$> f e
    go (PAtom b e1 e2) = PAtom b <$> f e1 <*> f e2
    go (PAll xs p)     = PAll xs <$> go p
    go PTop            = return PTop

--------------------------------------------------------------------------------
-- Expand Preds ----------------------------------------------------------------
--------------------------------------------------------------------------------

expandPred :: Pred -> BareM Pred
expandPred (PBexp e@(EApp (Loc l f') es))
  = do env <- gets (predAliases.rtEnv)
       case M.lookup f' env of
         Just rp ->
           return $ expandApp l rp es
         Nothing ->
           PBexp <$> expandExpr e

expandPred (PBexp e)
  = PBexp <$> expandExpr e

expandPred (PAnd ps)
  = PAnd <$> mapM expandPred ps
expandPred (POr ps)
  = POr <$> mapM expandPred ps

expandPred (PNot p)
  = PNot <$> expandPred p
expandPred (PAll xts p)
  = PAll xts <$> expandPred p

expandPred (PImp p q)
  = PImp <$> expandPred p <*> expandPred q
expandPred (PIff p q)
  = PIff <$> expandPred p <*> expandPred q

expandPred p@(PAtom _ _ _)
  = return p

expandPred PTrue
  = return PTrue
expandPred PFalse
  = return PFalse
expandPred PTop
  = return PTop

--------------------------------------------------------------------------------
-- Expand Exprs ----------------------------------------------------------------
--------------------------------------------------------------------------------

expandExpr :: Expr -> BareM Expr
expandExpr (EApp f@(Loc l f') es)
  = do env <- gets (exprAliases.rtEnv)
       case M.lookup f' env of
         Just re ->
           expandApp l re <$> mapM expandExpr es
         Nothing ->
           EApp f <$> mapM expandExpr es

expandExpr (EBin op e1 e2)
  = EBin op <$> expandExpr e1 <*> expandExpr e2
expandExpr (EIte p e1 e2)
  = EIte p <$> expandExpr e1 <*> expandExpr e2
expandExpr (ECst e s)
  = (`ECst` s) <$> expandExpr e

expandExpr e@(ESym _)
  = return e
expandExpr e@(ECon _)
  = return e
expandExpr e@(EVar _)
  = return e
expandExpr e@(ELit _ _)
  = return e

expandExpr EBot
  = return EBot

--------------------------------------------------------------------------------
-- Expand Alias Application ----------------------------------------------------
--------------------------------------------------------------------------------

expandApp l re es
  = subst su $ rtBody re
  where su  = mkSubst $ safeZipWithError msg (rtVArgs re) es
        msg = "Malformed alias application at " ++ show l ++ "\n\t"
               ++ show (rtName re) 
               ++ " defined at " ++ show (rtPos re)
               ++ "\n\texpects " ++ show (length $ rtVArgs re)
               ++ " arguments but it is given " ++ show (length es)

