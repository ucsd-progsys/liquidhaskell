{-# LANGUAGE CPP                       #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE PatternSynonyms           #-}

-- | This module contains a wrappers and utility functions for
-- accessing GHC module information. It should NEVER depend on
module Language.Haskell.Liquid.GHC.TypeRep (
  pattern FunTy, 
  module TyCoRep, 

  mkTyArg

  , showTy
  ) where

import TyCoRep
import Type 

import           Language.Haskell.Liquid.GHC.Misc (showPpr)
import           Language.Fixpoint.Types (symbol)

mkTyArg :: TyVar -> TyBinder
mkTyArg v = Named v Visible

pattern FunTy tx t = ForAllTy (Anon tx) t 

instance Eq Type where
  t1 == t2 = eqType' t1 t2



eqType' :: Type -> Type -> Bool 
eqType' (LitTy l1) (LitTy l2) 
  = l1 == l2  
eqType' (CoercionTy c1) (CoercionTy c2) 
  = c1 == c2  
eqType'(CastTy t1 c1) (CastTy t2 c2) 
  = eqType' t1 t2 && c1 == c2 
eqType' (ForAllTy (Named v1 _) t1) (ForAllTy (Named v2 _) t2) 
  = eqType' t1 (substTy (zipTvSubst [v2] [TyVarTy v1]) t2) 
eqType' (ForAllTy (Anon t11) t1) (ForAllTy (Anon t12) t2) 
  = eqType' t11 t12 && eqType' t1 t2 
eqType' (TyVarTy v1) (TyVarTy v2) 
  = v1 == v2 
eqType' (AppTy t11 t12) (AppTy t21 t22) 
  = eqType' t11 t21 && eqType' t12 t22  
eqType' (TyConApp c1 ts1) (TyConApp c2 ts2) 
  = c1 == c2 && and (zipWith eqType' ts1 ts2) 
eqType' _ _
  = False 


instance Eq TyBinder where
  (Named v1 f1) == (Named v2 f2) = v1 == v2 && f1 == f2  
  (Anon t1)     == (Anon t2)     = t1 == t2 
  _             == _             = False 

instance Eq Coercion where
  _ == _ = True 




showTy :: Type -> String 
showTy (TyConApp c ts) = "(RApp   " ++ showPpr c ++ " " ++ sep' ", " (showTy <$> ts) ++ ")"
showTy (AppTy t1 t2)   = "(TAppTy " ++ (showTy t1 ++ " " ++ showTy t2) ++ ")" 
showTy (TyVarTy v)   = "(RVar " ++ show (symbol v)  ++ ")" 
showTy (ForAllTy (Named v _) t)  = "ForAllTy " ++ show (symbol v) ++ ". (" ++  showTy t ++ ")"
showTy (ForAllTy (Anon t1) t2)  = "ForAllTy " ++ showTy t1 ++ ". (" ++  showTy t2 ++ ")"
showTy (CastTy _ _)    = "CastTy"
showTy (CoercionTy _)  = "CoercionTy"
showTy (LitTy _)       = "LitTy"

sep' :: String -> [String] -> String
sep' _ [x] = x
sep' _ []  = []
sep' s (x:xs) = x ++ s ++ sep' s xs 