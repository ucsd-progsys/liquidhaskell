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

expandReft :: RReft -> BareM RReft
expandReft = txPredReft expandPred expandExpr

txPredReft :: (Pred -> BareM Pred) -> (Expr -> BareM Expr) -> RReft -> BareM RReft
txPredReft f fe u = (\r -> u {ur_reft = r}) <$> txPredReft' (ur_reft u)
  where
    txPredReft' (Reft (v, ra)) = Reft . (v,) <$> txPredRefa ra
    txPredRefa  (Refa p)       = Refa        <$> (f <=< mapPredM fe) p

mapPredM :: (Expr -> BareM Expr) -> Pred -> BareM Pred
mapPredM f = go
  where
    go PTrue           = return PTrue
    go PFalse          = return PFalse
    go p@(PKVar _ _)   = return p
    go (PAnd ps)       = PAnd <$> mapM go ps
    go (POr ps)        = POr  <$> mapM go ps
    go (PNot p)        = PNot <$> go p
    go (PImp p q)      = PImp <$> go p <*> go q
    go (PIff p q)      = PIff <$> go p <*> go q
    go (PBexp e)       = PBexp <$> f e
    go (PAtom b e1 e2) = PAtom b <$> f e1 <*> f e2
    go (PAll xs p)     = PAll xs <$> go p
    go (PEx xs p)      = PEx  xs <$> go p
    go PTop            = return PTop

--------------------------------------------------------------------------------
-- Expand Preds ----------------------------------------------------------------
--------------------------------------------------------------------------------

expandPred :: Pred -> BareM Pred

expandPred p@(PBexp (EApp (Loc l _ f') es))
  = do env <- gets (predAliases.rtEnv)
       return $
         case M.lookup f' env of
           Just rp ->
             expandApp l rp es
           Nothing ->
             p
expandPred p@(PBexp _)
  = return p
expandPred (PAnd ps)
  = PAnd <$> mapM expandPred ps
expandPred (POr ps)
  = POr <$> mapM expandPred ps
expandPred (PNot p)
  = PNot <$> expandPred p
expandPred (PImp p q)
  = PImp <$> expandPred p <*> expandPred q
expandPred (PIff p q)
  = PIff <$> expandPred p <*> expandPred q
expandPred (PAll xs p)
  = PAll xs <$> expandPred p
expandPred (PEx xs p)
  = PEx xs <$> expandPred p
expandPred p
  = return p

--------------------------------------------------------------------------------
-- Expand Exprs ----------------------------------------------------------------
--------------------------------------------------------------------------------

expandExpr :: Expr -> BareM Expr

expandExpr (EApp f@(Loc l _ f') es)
  = do env <- gets (exprAliases.rtEnv)
       case M.lookup f' env of
         Just re ->
           expandApp l re <$> mapM expandExpr es
         Nothing ->
           EApp f <$> mapM expandExpr es

expandExpr (ENeg e)
  = ENeg <$> expandExpr e
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
