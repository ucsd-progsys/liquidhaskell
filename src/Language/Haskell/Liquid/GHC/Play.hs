{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE PatternSynonyms           #-}

module Language.Haskell.Liquid.GHC.Play where

import Prelude hiding (error)
import GHC
import CoreSyn
import Var
import TyCoRep hiding (substTysWith)
import DataCon

import TyCon
import Type      (tyConAppArgs_maybe, tyConAppTyCon_maybe, binderVar)
import PrelNames (isStringClassName)

import           Control.Arrow       ((***))
import qualified Data.HashMap.Strict as M

import Language.Haskell.Liquid.GHC.Misc ()
import Language.Haskell.Liquid.Types.Errors

dataConImplicitIds :: DataCon -> [Id]
dataConImplicitIds dc = [ x | AnId x <- dataConImplicitTyThings dc]

class Subable a where
  sub   :: M.HashMap CoreBndr CoreExpr -> a -> a
  subTy :: M.HashMap TyVar Type -> a -> a

instance Subable CoreExpr where
  sub s (Var v)        = M.lookupDefault (Var v) v s
  sub _ (Lit l)        = Lit l
  sub s (App e1 e2)    = App (sub s e1) (sub s e2)
  sub s (Lam b e)      = Lam b (sub s e)
  sub s (Let b e)      = Let (sub s b) (sub s e)
  sub s (Case e b t a) = Case (sub s e) (sub s b) t (map (sub s) a)
  sub s (Cast e c)     = Cast (sub s e) c
  sub s (Tick t e)     = Tick t (sub s e)
  sub _ (Type t)       = Type t
  sub _ (Coercion c)   = Coercion c

  subTy s (Var v)      = Var (subTy s v)
  subTy _ (Lit l)      = Lit l
  subTy s (App e1 e2)  = App (subTy s e1) (subTy s e2)
  subTy s (Lam b e)    | isTyVar b = Lam v' (subTy s e)
   where v' = case M.lookup b s of
               Just (TyVarTy v) -> v
               _                -> b

  subTy s (Lam b e)      = Lam (subTy s b) (subTy s e)
  subTy s (Let b e)      = Let (subTy s b) (subTy s e)
  subTy s (Case e b t a) = Case (subTy s e) (subTy s b) (subTy s t) (map (subTy s) a)
  subTy s (Cast e c)     = Cast (subTy s e) (subTy s c)
  subTy s (Tick t e)     = Tick t (subTy s e)
  subTy s (Type t)       = Type (subTy s t)
  subTy s (Coercion c)   = Coercion (subTy s c)

instance Subable Coercion where
  sub _ c                = c
  subTy _ _              = panic Nothing "subTy Coercion"

instance Subable (Alt Var) where
 sub s (a, b, e)   = (a, map (sub s) b,   sub s e)
 subTy s (a, b, e) = (a, map (subTy s) b, subTy s e)

instance Subable Var where
 sub s v   | M.member v s = subVar $ s M.! v
           | otherwise    = v
 subTy s v = setVarType v (subTy s (varType v))

subVar :: Expr t -> Id
subVar (Var x) = x
subVar  _      = panic Nothing "sub Var"

instance Subable (Bind Var) where
 sub s (NonRec x e)   = NonRec (sub s x) (sub s e)
 sub s (Rec xes)      = Rec ((sub s *** sub s) <$> xes)

 subTy s (NonRec x e) = NonRec (subTy s x) (subTy s e)
 subTy s (Rec xes)    = Rec ((subTy s  *** subTy s) <$> xes)

instance Subable Type where
 sub _ e   = e
 subTy     = substTysWith

substTysWith :: M.HashMap Var Type -> Type -> Type
substTysWith s tv@(TyVarTy v)  = M.lookupDefault tv v s
substTysWith s (FunTy t1 t2)   = FunTy (substTysWith s t1) (substTysWith s t2)
substTysWith s (ForAllTy v t)  = ForAllTy v (substTysWith (M.delete (binderVar v) s) t)
substTysWith s (TyConApp c ts) = TyConApp c (map (substTysWith s) ts)
substTysWith s (AppTy t1 t2)   = AppTy (substTysWith s t1) (substTysWith s t2)
substTysWith _ (LitTy t)       = LitTy t
substTysWith s (CastTy t c)    = CastTy (substTysWith s t) c
substTysWith _ (CoercionTy c)  = CoercionTy c 

substExpr :: M.HashMap Var Var -> CoreExpr -> CoreExpr
substExpr s = go 
  where
    subsVar v                = M.lookupDefault v v s
    go (Var v)               = Var $ subsVar v
    go (Lit l)               = Lit l 
    go (App e1 e2)           = App (go e1) (go e2) 
    go (Lam x e)             = Lam (subsVar x) (go e)
    go (Let (NonRec x ex) e) = Let (NonRec (subsVar x) (go ex)) (go e) 
    go (Let (Rec xes) e)     = Let (Rec [(subsVar x, go e) | (x,e) <- xes]) (go e)
    go (Case e b t alts)     = Case (go e) (subsVar b) t [(c, subsVar <$> xs, go e) | (c, xs, e) <- alts]
    go (Cast e c)            = Cast (go e) c 
    go (Tick t e)            = Tick t (go e)
    go (Type t)              = Type t 
    go (Coercion c)          = Coercion c 

mapType :: (Type -> Type) -> Type -> Type
mapType f = go
  where
    go t@(TyVarTy _)   = f t
    go (AppTy t1 t2)   = f $ AppTy (go t1) (go t2)
    go (TyConApp c ts) = f $ TyConApp c (go <$> ts)
    go (FunTy t1 t2)   = f $ FunTy (go t1) (go t2)
    go (ForAllTy v t)  = f $ ForAllTy v (go t)
    go t@(LitTy _)     = f t
    go (CastTy t c)    = CastTy (go t) c
    go (CoercionTy c)  = f $ CoercionTy c 


stringClassArg :: Type -> Maybe Type
stringClassArg t
  = case (tyConAppTyCon_maybe t, tyConAppArgs_maybe t) of
      (Just c, Just [t]) | isStringClassName == tyConName c
           -> Just t
      _    -> Nothing
