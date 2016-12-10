{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Bare.Expand (
    ExpandAliases (..)
  -- , expandReft
  -- , expandExpr
  ) where

import           Prelude                          hiding (error)
import           Control.Monad.State              hiding (forM)
import qualified Data.HashMap.Strict              as M
import           Language.Fixpoint.Types          (Expr(..), Reft(..), mkSubst, subst, eApps, splitEApp, Symbol, Subable)
import           Language.Haskell.Liquid.Misc     (safeZipWithError)
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Bare.Env

class ExpandAliases a where
  expand :: a -> BareM a

-- instance (ExpandAliases a) => ExpandAliases (UReft a) where
  -- expand (MkUReft a y z) = (\b -> MkUReft b y z) <$> expand a

instance ExpandAliases Expr where
  expand = expandExpr

instance ExpandAliases Reft where
  expand = txPredReft' expandExpr


instance ExpandAliases SpecType where
  expand = mapReftM expand

instance (ExpandAliases b) => ExpandAliases (a, b) where
  -- expand (x, y) = (x, ) <$> expand y
  expand = mapM expand -- (x, y) = (x, ) <$> expand y

instance ExpandAliases RReft where
  expand = mapM expand

instance (ExpandAliases a) => ExpandAliases (Located a) where
  expand = mapM expand

instance (ExpandAliases a) => ExpandAliases [a] where
  expand = mapM expand

--------------------------------------------------------------------------------
-- Expand Reft Preds & Exprs ---------------------------------------------------
--------------------------------------------------------------------------------
-- expandReft :: RReft -> BareM RReft
-- expandReft = txPredReft expandExpr
--
-- txPredReft :: (Expr -> BareM Expr) -> RReft -> BareM RReft
-- txPredReft f u = (\r -> u {ur_reft = r}) <$> txPredReft' f (ur_reft u)

txPredReft' :: (Expr -> BareM Expr) -> Reft -> BareM Reft
txPredReft' f (Reft (v, ra)) = Reft . (v,) <$> f ra

--------------------------------------------------------------------------------
-- Expand Exprs ----------------------------------------------------------------
--------------------------------------------------------------------------------
expandExpr :: Expr -> BareM Expr
expandExpr e@(EApp _ _)
  = expandEApp $ splitEApp e
expandExpr (ENeg e)
  = ENeg <$> expandExpr e
expandExpr (EBin op e1 e2)
  = EBin op <$> expandExpr e1 <*> expandExpr e2
expandExpr (EIte p e1 e2)
  = EIte <$> expandExpr p <*> expandExpr e1 <*> expandExpr e2
expandExpr (ECst e s)
  = (`ECst` s) <$> expandExpr e

expandExpr e@(EVar _)
  = return e
expandExpr e@(ESym _)
  = return e
expandExpr e@(ECon _)
  = return e

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
expandExpr (ELam xt e)
  = ELam xt <$> expandExpr e

expandExpr (ETApp e s)
  = (`ETApp` s) <$> expandExpr e
expandExpr (ETAbs e s)
  = (`ETAbs` s) <$> expandExpr e

expandExpr (PAtom b e1 e2)
  = PAtom b <$> expandExpr e1 <*> expandExpr e2

expandExpr (PKVar k s)
  = return $ PKVar k s

expandExpr PGrad
  = return PGrad

expandExpr (PExist s e)
  = PExist s <$> expandExpr e


expandEApp :: (Expr,[Expr]) -> BareM Expr
expandEApp (EVar f, es)
  = do env <- gets (exprAliases . rtEnv)
       case M.lookup f env of
         Just re ->
           expandApp re <$> mapM expandExpr es
         Nothing ->
           eApps (EVar f) <$> mapM expandExpr es
expandEApp (f, es)
  = return $ eApps f es

--------------------------------------------------------------------------------
-- Expand Alias Application ----------------------------------------------------
--------------------------------------------------------------------------------

expandApp
  :: Subable ty =>
     RTAlias Symbol ty -> [Expr] -> ty
expandApp re es
  = subst su $ rtBody re
  where su  = mkSubst $ safeZipWithError msg (rtVArgs re) es
        msg = "Malformed alias application" ++ "\n\t"
               ++ show (rtName re)
               ++ " defined at " ++ show (rtPos re)
               ++ "\n\texpects " ++ show (length $ rtVArgs re)
               ++ " arguments but it is given " ++ show (length es)
