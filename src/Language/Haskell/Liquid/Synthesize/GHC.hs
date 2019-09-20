{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
module Language.Haskell.Liquid.Synthesize.GHC where

import Var 
import TyCoRep
import CoreSyn

import IdInfo
import OccName
import Unique 
import Name 
import TysPrim


import Data.Default
import Data.Maybe (fromMaybe)
import           Data.List 
import Language.Haskell.Liquid.GHC.TypeRep
import Language.Fixpoint.Types
instance Default Type where
    def = TyVarTy alphaTyVar 
    
-- JP: Let's try to avoid this.
-- instance Default CoreExpr where 
--     def = Var $ mkVar (Just "undefined") 0 def

mkVar :: Maybe String -> Int -> Type -> Var
mkVar x i t = mkGlobalVar VanillaId name t vanillaIdInfo 
  where 
    name = mkSystemName (mkUnique 'S' i) (mkVarOcc x')
    x'   = fromMaybe (freshName i) x 

freshName :: Int -> String 
freshName i = "lSyn$" ++ show i 

-- Select all functions with result type equal with goalType
--        | goal |
goalType :: Type -> Type -> Bool
goalType τ t@(ForAllTy (TvBndr var _) htype) = 
  let substHType = substInType htype (varsInType τ)
  in  goalType τ substHType
goalType τ t@(FunTy _ t'') -- τ: base types
  | t'' == τ  = True
  | otherwise = goalType τ t''
goalType τ                 t 
  | τ == t    = True
  | otherwise = False


-- Subgoals are function's arguments.
createSubgoals :: Type -> [Type] 
createSubgoals (ForAllTy _ htype) = createSubgoals htype
createSubgoals (FunTy t1 t2)      = t1 : createSubgoals t2
createSubgoals t                  = [t]


-- Removes forall from type and replaces
-- type variables from the first argument to the second argument.
-- Returns the new type.
-- TODO: Instead of substituting type variables, perform type applications
-- and then, get the type.
instantiateType :: Type -> Type -> Type 
instantiateType τ t = 
  let t' = substInType t (varsInType τ)
  in  case t' of 
        ForAllTy _ t'' -> t''
        _              -> t' 

-- TODO: More than one type variables in type (what happens in forall case with that?).
-- use Language.Haskell.Liquid.GHC.TypeRep.subst instead 
substInType :: Type -> [TyVar] -> Type 
substInType t [tv] = substInType' tv t
  where 
    substInType' tv (TyVarTy var)                = TyVarTy tv
    substInType' tv (ForAllTy (TvBndr var x) ty) = ForAllTy (TvBndr tv x) (substInType' tv ty)
    substInType' tv (FunTy t0 t1)                = FunTy (substInType' tv t0) (substInType' tv t1)
    substInType' tv (AppTy t0 t1)                = AppTy (substInType' tv t0) (substInType' tv t1)
    substInType' tv (TyConApp c ts)              = TyConApp c (map (substInType' tv) ts)
    substInType' _  t                            = error $ "[substInType'] Shouldn't reach that point for now " ++ showTy t
substInType _ vars = error $ "My example has one type variable. Vars: " ++ show (map symbol vars)

-- Find all variables in type
varsInType :: Type -> [TyVar] 
varsInType t = (map head . group . sort) (varsInType' t)
  where
    varsInType' (TyVarTy var)                = [var]
    varsInType' (ForAllTy (TvBndr var _) ty) = var : varsInType' ty
    varsInType' (FunTy t0 t1)                = varsInType' t0 ++ varsInType' t1
    varsInType' (AppTy t0 t1)                = varsInType' t0 ++ varsInType' t1 
    varsInType' (TyConApp c ts)              = foldr (\x y -> concatMap varsInType' ts ++ y) [] ts
    varsInType' t                            = error $ "[varsInType] Shouldn't reach that point for now " ++ showTy t

-- If you find a binding add it to the second argument.
--                    | (lhs, rhs)      |
fromAnf :: CoreExpr -> [(Var, CoreExpr)] -> (CoreExpr, [(Var, CoreExpr)])
fromAnf (Let bnd e) bnds       = 
  case bnd of
    Rec {}       -> error "No recursive bindings in let."
    NonRec rb lb -> 
      fromAnf e ((rb, replaceBnds lb' bnds') : bnds')
        where (lb', bnds')     = fromAnf lb bnds
fromAnf (Case scr bnd tp alts) bnds
  = (Case scr bnd tp (map (\(altc, xs, e) -> (altc, xs, fst $ fromAnf e bnds)) alts), bnds)
fromAnf e           bnds       = (replaceBnds e bnds, bnds)


replaceBnds :: CoreExpr -> [(Var, CoreExpr)] -> CoreExpr 
replaceBnds (Var var) bnds    = fromMaybe (Var var) (lookup var bnds)
replaceBnds (App e1 e2) bnds  = App (replaceBnds e1 bnds) (replaceBnds e2 bnds) 
replaceBnds (Type t)    _     = Type t
replaceBnds lit@Lit{}   _     = lit 
replaceBnds e           _     = e
