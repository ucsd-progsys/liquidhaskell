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
expandReft = txPredReft expandExpr

txPredReft :: (Expr -> BareM Expr) -> RReft -> BareM RReft
txPredReft f u = (\r -> u {ur_reft = r}) <$> txPredReft' (ur_reft u)
  where
    txPredReft' (Reft (v, ra)) = Reft . (v,) <$> f ra 

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
  = EIte <$> expandExpr p <*> expandExpr e1 <*> expandExpr e2
expandExpr (ECst e s)
  = (`ECst` s) <$> expandExpr e

expandExpr e@(ESym _)
  = return e
expandExpr e@(ECon _)
  = return e
expandExpr e@(EVar _)
  = return e

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

expandExpr (ETApp e s)
  = (`ETApp` s) <$> expandExpr e 
expandExpr (ETAbs e s)
  = (`ETAbs` s) <$> expandExpr e 

expandExpr PTrue 
  = return PTrue
expandExpr PFalse
  = return PFalse
expandExpr PTop
  = return PTop

expandExpr (PAtom b e1 e2)
  = PAtom b <$> expandExpr e1 <*> expandExpr e2 

expandExpr (PKVar k s)
  = return $ PKVar k s 

expandExpr (PExist s e)
  = PExist s <$> expandExpr e 

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
