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

  mkTyArg, 

  showTy
  ) where

import TyCoRep
import Coercion
import CoAxiom
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
  = eqType' t1 (subst v2 (TyVarTy v1) t2) 
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



-------------------------------------------------------------------------------
-- | GHC Type Substitutions ---------------------------------------------------
-------------------------------------------------------------------------------

class SubstTy a where
  subst :: TyVar -> Type -> a -> a
  subst _ _ = id  

instance SubstTy Type where
  subst = substType

substType :: TyVar -> Type -> Type -> Type
substType x tx (TyConApp c ts) 
  = TyConApp c (subst x tx <$> ts)
substType x tx (AppTy t1 t2)   
  = AppTy (subst x tx t1) (subst x tx t2) 
substType x tx (TyVarTy y)   
  | symbol x == symbol y
  = tx 
  | otherwise
  = TyVarTy y 
substType x tx (ForAllTy (Named y v) t)  
  | symbol x == symbol y 
  = (ForAllTy (Named y v) t)
  | otherwise 
  = ForAllTy (Named y v) (subst x tx t)
substType x tx (ForAllTy (Anon t1) t2)  
  = ForAllTy (Anon (subst x tx t1)) (subst x tx t2)
substType x tx (CastTy t c)    
  = CastTy (subst x tx t) (subst x tx c)
substType x tx (CoercionTy c)  
  = CoercionTy $ subst x tx c 
substType _ _  (LitTy l)
  = LitTy l  


instance SubstTy Coercion where
  subst = substCoercion

substCoercion :: TyVar -> Type -> Coercion -> Coercion
substCoercion x tx (Refl r t)
  = Refl (subst x tx r) (subst x tx t)
substCoercion x tx (TyConAppCo r c cs)
  = TyConAppCo (subst x tx r) c (subst x tx <$> cs)
substCoercion x tx (AppCo c1 c2)
  = AppCo (subst x tx c1) (subst x tx c2)
substCoercion x tx (ForAllCo y c1 c2)
  | symbol x == symbol y 
  = (ForAllCo y c1 c2)
  | otherwise 
  = ForAllCo y (subst x tx c1) (subst x tx c2)
substCoercion _ _ (CoVarCo y)
  = CoVarCo y 
substCoercion x tx (AxiomInstCo co bi cs)
  = AxiomInstCo (subst x tx co) bi (subst x tx <$> cs)  
substCoercion x tx (UnivCo y r t1 t2)
  = UnivCo (subst x tx y) (subst x tx r) (subst x tx t1) (subst x tx t2)
substCoercion x tx (SymCo c)
  = SymCo (subst x tx c)
substCoercion x tx (TransCo c1 c2)
  = TransCo (subst x tx c1) (subst x tx c2)
substCoercion x tx (AxiomRuleCo ca cs)
  = AxiomRuleCo (subst x tx ca)  (subst x tx <$> cs)  
substCoercion x tx (NthCo i c)
  = NthCo i (subst x tx c)
substCoercion x tx (LRCo i c)
  = LRCo i (subst x tx c)
substCoercion x tx (InstCo c1 c2)
  = InstCo (subst x tx c1) (subst x tx c2)
substCoercion x tx (CoherenceCo c1 c2)
  = CoherenceCo (subst x tx c1) (subst x tx c2)
substCoercion x tx (KindCo c)
  = KindCo (subst x tx c)
substCoercion x tx (SubCo c)
  = SubCo (subst x tx c)


instance SubstTy Role where
instance SubstTy (CoAxiom Branched) where

instance SubstTy UnivCoProvenance where
  subst x tx (PhantomProv c)
    = PhantomProv $ subst x tx c 
  subst x tx (ProofIrrelProv c)
    = ProofIrrelProv $ subst x tx c 
  subst _ _ ch 
    = ch 

instance SubstTy CoAxiomRule where
  subst x tx (CoAxiomRule n rs r ps) 
    = CoAxiomRule n (subst x tx <$> rs) (subst x tx r) (\eq -> subst x tx (ps (subst x tx eq)))

instance (SubstTy a, Functor m) => SubstTy (m a) where
  subst x tx xs = subst x tx <$> xs
