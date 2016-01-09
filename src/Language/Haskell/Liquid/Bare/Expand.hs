{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bare.Expand (
    expandReft
  , expandExpr
  ) where

import Prelude hiding (error)
import Control.Monad.Reader hiding (forM)
import Control.Monad.State hiding (forM)

import qualified Data.HashMap.Strict as M

import Language.Fixpoint.Types (Expr(..), Reft(..), mkSubst, subst)

import Language.Haskell.Liquid.Misc (safeZipWithError)
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Types.Errors

import Language.Haskell.Liquid.Bare.Env

--------------------------------------------------------------------------------
-- Expand Reft Preds & Exprs ---------------------------------------------------
--------------------------------------------------------------------------------

expandReft :: RReft -> BareM RReft
expandReft = txPredReft expandExpr expandExpr

txPredReft :: (Expr -> BareM Expr) -> (Expr -> BareM Expr) -> RReft -> BareM RReft
txPredReft f fe u = (\r -> u {ur_reft = r}) <$> txPredReft' (ur_reft u)
  where
    txPredReft' (Reft (v, ra)) = Reft . (v,) <$> txPredRefa ra
    txPredRefa                 = (f <=< mapPredM fe)

mapPredM :: (Expr -> BareM Expr) -> Expr -> BareM Expr
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
    go (PAtom b e1 e2) = PAtom b <$> f e1 <*> f e2
    go (PAll xs p)     = PAll xs <$> go p
    go (PExist _ _)    = panic Nothing "mapPredM: PExist is for fixpoint internals only"
    -- go (PExist xs p)   = PExist xs <$> go p
    go PTop            = return PTop
    go (ESym s)        = return $ ESym s 
    go (ECon c)        = return $ ECon c 
    go (EVar v)        = return $ EVar v 
    go (EApp s es)     = EApp s <$> mapM go es 
    go (ENeg e)        = ENeg <$> go e 
    go (EBin b e1 e2)  = EBin b <$> go e1 <*> go e2 
    go (EIte e e1 e2)  = EIte <$> go e <*> go e1 <*> go e2 
    go (ECst e s)      = (`ECst` s) <$> go e 
    go EBot            = return EBot
    go (ETApp e s)     = (`ETApp` s) <$> go e 
    go (ETAbs e s)     = (`ETAbs` s) <$> go e 

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
--expandExpr e@(ELit _ _)
--  = return e

expandExpr EBot
  = return EBot

expandExpr (PAnd ps)
  = PAnd <$> mapM expandExpr ps
expandExpr (POr ps)
  = POr <$> mapM expandExpr ps
expandExpr (PNot p)
  = PNot <$> expandExpr p
expandExpr (PImp p q)
  = PImp <$> expandExpr p <*> expandExpr q
expandExpr (PIff p q)
  = PIff <$> expandExpr p <*> expandExpr q
expandExpr (PAll xs p)
  = PAll xs <$> expandExpr p
-- expandExpr (PExist xs p)
--   = PExist xs <$> expandExpr p
expandExpr p
  = return p

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
