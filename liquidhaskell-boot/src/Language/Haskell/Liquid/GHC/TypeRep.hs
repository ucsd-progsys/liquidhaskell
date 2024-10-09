{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE StandaloneDeriving        #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- TODO(#1918): Only needed for GHC <9.0.1.
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Haskell.Liquid.GHC.TypeRep (
  mkTyArg, 

  showTy
  ) where

import           Language.Haskell.Liquid.GHC.Misc (showPpr)
import           Liquid.GHC.API as Ghc hiding (mkTyArg, showPpr, panic)
import           Language.Fixpoint.Types (symbol)

-- e368f3265b80aeb337fbac3f6a70ee54ab14edfd

mkTyArg :: TyVar -> TyVarBinder
mkTyArg v = Bndr v Required

instance Eq Type where
  t1 == t2 = eqType' t1 t2

eqType' :: Type -> Type -> Bool 
eqType' (LitTy l1) (LitTy l2) 
  = l1 == l2  
eqType' (CoercionTy _c1) (CoercionTy _c2) = True
eqType'(CastTy t1 _c1) (CastTy t2 _c2) = eqType' t1 t2
eqType' (FunTy a1 m1 t11 t12) (FunTy a2 m2 t21 t22)
  = a1 == a2 && m1 == m2 && eqType' t11 t21 && eqType' t12 t22  
eqType' (ForAllTy (Bndr v1 _) t1) (ForAllTy (Bndr v2 _) t2) 
  = eqType' t1 (substType v2 (TyVarTy v1) t2)
eqType' (TyVarTy v1) (TyVarTy v2) 
  = v1 == v2 
eqType' (AppTy t11 t12) (AppTy t21 t22) 
  = eqType' t11 t21 && eqType' t12 t22  
eqType' (TyConApp c1 ts1) (TyConApp c2 ts2) 
  = c1 == c2 && and (zipWith eqType' ts1 ts2) 
eqType' _ _ 
  = False 


deriving instance (Eq tyvar, Eq argf) => Eq (VarBndr tyvar argf)

showTy :: Type -> String 
showTy (TyConApp c ts) = "(RApp   " ++ showPpr c ++ " " ++ sep' ", " (showTy <$> ts) ++ ")"
showTy (AppTy t1 t2)   = "(TAppTy " ++ (showTy t1 ++ " " ++ showTy t2) ++ ")" 
showTy (TyVarTy v)   = "(RVar " ++ show (symbol v)  ++ ")" 
showTy (ForAllTy (Bndr v _) t)  = "ForAllTy " ++ show (symbol v) ++ ". (" ++  showTy t ++ ")"
showTy (FunTy af _m1 t1 t2) = "FunTy " ++ showPpr af ++ " " ++ showTy t1 ++ ". (" ++  showTy t2 ++ ")"
showTy (CastTy _ _)    = "CastTy"
showTy (CoercionTy _)  = "CoercionTy"
showTy (LitTy _)       = "LitTy"

sep' :: String -> [String] -> String
sep' _ [x] = x
sep' _ []  = []
sep' s (x:xs) = x ++ s ++ sep' s xs 



-------------------------------------------------------------------------------
-- | GHC Type Substitutions ---------------------------------------------------
-------------------------------------------------------------------------------

substType :: TyVar -> Type -> Type -> Type
substType x tx (TyConApp c ts) 
  = TyConApp c (substType x tx <$> ts)
substType x tx (AppTy t1 t2)   
  = AppTy (substType x tx t1) (substType x tx t2)
substType x tx (TyVarTy y)   
  | symbol x == symbol y
  = tx 
  | otherwise
  = TyVarTy y 
substType x tx (FunTy aaf m t1 t2)
  = FunTy aaf m (substType x tx t1) (substType x tx t2)
substType x tx f@(ForAllTy b@(Bndr y _) t)  
  | symbol x == symbol y 
  = f
  | otherwise 
  = ForAllTy b (substType x tx t)
substType x tx (CastTy t c)    
  = let ss = extendSubstInScopeSet (zipTvSubst [x] [tx]) (tyCoVarsOfCo c)
     in CastTy (substType x tx t) (substCo ss c)
substType x tx (CoercionTy c)  
  = let ss = extendSubstInScopeSet (zipTvSubst [x] [tx]) (tyCoVarsOfCo c)
     in CoercionTy $ substCo ss c
substType _ _  (LitTy l)
  = LitTy l  

