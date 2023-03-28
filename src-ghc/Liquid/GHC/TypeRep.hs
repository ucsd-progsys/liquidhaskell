{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE StandaloneDeriving        #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- TODO(#1918): Only needed for GHC <9.0.1.
{-# OPTIONS_GHC -Wno-orphans #-}

module Liquid.GHC.TypeRep (
  mkTyArg, 

  showTy
  ) where

import           Liquid.GHC.Misc (showPpr)
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
eqType' (CoercionTy c1) (CoercionTy c2) 
  = c1 == c2  
eqType'(CastTy t1 c1) (CastTy t2 c2) 
  = eqType' t1 t2 && c1 == c2 
eqType' (FunTy a1 m1 t11 t12) (FunTy a2 m2 t21 t22)
  = a1 == a2 && m1 == m2 && eqType' t11 t21 && eqType' t12 t22  
eqType' (ForAllTy (Bndr v1 _) t1) (ForAllTy (Bndr v2 _) t2) 
  = eqType' t1 (subst v2 (TyVarTy v1) t2) 
eqType' (TyVarTy v1) (TyVarTy v2) 
  = v1 == v2 
eqType' (AppTy t11 t12) (AppTy t21 t22) 
  = eqType' t11 t21 && eqType' t12 t22  
eqType' (TyConApp c1 ts1) (TyConApp c2 ts2) 
  = c1 == c2 && and (zipWith eqType' ts1 ts2) 
eqType' _ _ 
  = False 


deriving instance (Eq tyvar, Eq argf) => Eq (VarBndr tyvar argf)

instance Eq Coercion where
  _ == _ = True 


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
substType x tx (FunTy aaf m t1 t2)
  = FunTy aaf m (subst x tx t1) (subst x tx t2)
substType x tx f@(ForAllTy b@(Bndr y _) t)  
  | symbol x == symbol y 
  = f
  | otherwise 
  = ForAllTy b (subst x tx t)
substType x tx (CastTy t c)    
  = CastTy (subst x tx t) (subst x tx c)
substType x tx (CoercionTy c)  
  = CoercionTy $ subst x tx c 
substType _ _  (LitTy l)
  = LitTy l  


instance SubstTy Coercion where
  subst = substCoercion

substCoercion :: TyVar -> Type -> Coercion -> Coercion
substCoercion x tx (TyConAppCo r c cs)
  = TyConAppCo (subst x tx r) c (subst x tx <$> cs)
substCoercion x tx (AppCo c1 c2)
  = AppCo (subst x tx c1) (subst x tx c2)
substCoercion x tx (FunCo r cN c1 c2)
  = FunCo r cN (subst x tx c1) (subst x tx c2) -- TODO(adinapoli) Is this the correct substitution?
substCoercion x tx (ForAllCo y c1 c2)
  | symbol x == symbol y 
  = ForAllCo y c1 c2
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
substCoercion x tx (NthCo r i c)
  = NthCo r i (subst x tx c)
substCoercion x tx (LRCo i c)
  = LRCo i (subst x tx c)
substCoercion x tx (InstCo c1 c2)
  = InstCo (subst x tx c1) (subst x tx c2)
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
