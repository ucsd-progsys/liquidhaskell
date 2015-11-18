{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Constraint.ProofToCore where

import CoreSyn hiding (Expr, Var)
import qualified CoreSyn as H

import Var hiding (Var)
import CoreUtils 

import Type hiding (Var)
import TypeRep 

import Language.Fixpoint.Misc (traceShow)

import Language.Haskell.Liquid.GhcMisc 

import Prover.Types 

import qualified Data.List as L
import Data.Maybe (fromMaybe)

type HId       = Id 
type HVar      = Var      HId 
type HAxiom    = Axiom    HId 
type HCtor     = Ctor     HId 
type HQuery    = Query    HId 
type HInstance = Instance HId 
type HProof    = Proof    HId 
type HExpr     = Expr     HId 

class ToCore a where
  toCore :: CoreExpr -> a -> CoreExpr 

instance ToCore HInstance where
  toCore e i = mkApp (toCore e $ inst_axiom i) (toCore e <$> inst_args i) 

instance ToCore HProof where
  toCore e Invalid = e
  toCore e p       = combineProofs e $ (toCore e <$> p_evidence p)

instance ToCore HAxiom where
  toCore e a = toCore e $ axiom_name a 
 
instance ToCore HExpr  where
  toCore e (EVar v)    = toCore e v 
  toCore e (EApp c es) = mkApp (toCore e c) (toCore e <$> es) 

instance ToCore HCtor where
  toCore e c =  toCore e $ ctor_var c 

instance ToCore HVar where
  toCore _ v = H.Var $ var_info v 

mkApp f es = traceShow ("\n\nmkApp " ++ show (exprType f) ++ "\n\nARGS \n\n" ++ (sep "\n" (showTy . exprType <$> es)) ++ "\n\nResolved Vars " ++ sep ", " (map showPair vts) ) $ 
                foldl (flip Let) (foldl App f' (reverse es')) bs  
  where
   vts = resolveVs as $ zip ts (exprType <$> es)
   (as, ts)  = bkArrow (exprType f)
   f' = instantiateVars vts f 
   (bs, es', _) = foldl anf ([], [], [1..]) ((instantiateVars vts) <$> es)

anf :: ([CoreBind], [CoreExpr], [Int]) -> CoreExpr -> ([CoreBind], [CoreExpr], [Int])
anf (bs, es, i:uniq) e@(App _ _) = ((NonRec v e):bs, H.Var v:es, uniq)
  where v = stringVar ("proof_anf" ++ show i) (exprType e)

anf (bs, es, uniq) e = (bs, e:es, uniq)  

instantiateVars vts e = go e (exprType e)
  where
    go :: CoreExpr -> Type -> CoreExpr
    go e (ForAllTy a t) = go (App e (Type $ fromMaybe (TyVarTy a) $ L.lookup a vts)) t  
    go e _ = e 

showPair (v, TyVarTy t) = show (tvId v) ++ " : " ++ show (tvId t) 
showPair (v, t) = show (tvId v) ++ " : " ++ show t 

showTy (ForAllTy a t) = "forall " ++ show (tvId a) ++ " . " ++ showTy t 
showTy (TyVarTy a)    = show (tvId a)
showTy (FunTy t1 t2)  = showTy t1 ++ " -> " ++ showTy t2  
showTy (TyConApp c ts)  = show c ++ sep " " (showTy <$> ts) 
showTy t = show t 


resolveVs :: [a] -> [(Type, Type)] -> [(Id, Type)]
resolveVs as [] = []
resolveVs as ((ForAllTy a t1, t2)     :ts) = resolveVs as ((t1, t2):ts)
resolveVs as ((t1, ForAllTy a t2)     :ts) = resolveVs as ((t1, t2):ts)
resolveVs as ((FunTy   t1 t2, FunTy t1' t2'):ts) = resolveVs as ((t1, t1'):(t2, t2'):ts)
resolveVs as ((AppTy t1 t2, AppTy t1' t2'):ts) = resolveVs as ((t1, t1'):(t2, t2'):ts)
resolveVs as ((TyVarTy a, TyVarTy a'):ts) | a == a' = resolveVs as ts 
resolveVs as ((TyVarTy a, t):ts)               = let vts = (resolveVs as (substTyV (a, t) <$> ts)) in (a, resolveVar a t vts) : vts 
resolveVs as ((t, TyVarTy a):ts)               = let vts = (resolveVs as (substTyV (a, t) <$> ts)) in (a, resolveVar a t vts) : vts 
resolveVs as ((TyConApp _ cts,TyConApp _ cts'):ts) = resolveVs as (zip cts cts' ++ ts)
resolveVs as ((LitTy _, LitTy _):ts) = resolveVs as ts 
resolveVs _ (tt:ts) = error $ showPpr tt


resolveVar a t [] = t 
resolveVar a t ((a', t'):ats) 
  | a == a'           = resolveVar a' t' ats 
  | TyVarTy a'' <- t' = resolveVar a'' t' ats 
  | otherwise         = resolveVar a t ats  
         

substTyV :: (Id, Type) -> (Type, Type) -> (Type, Type)
substTyV (a, at) (t1, t2) = (go t1, go t2)
  where
    go (ForAllTy a' t) | a == a'   = ForAllTy a' t
                       | otherwise = ForAllTy a' (go t)
    go (FunTy t1 t2) = FunTy (go t1) (go t2)
    go (AppTy t1 t2) = AppTy (go t1) (go t2)
    go (TyConApp c ts) = TyConApp c (go <$> ts)
    go (LitTy l)       = LitTy l 
    go (TyVarTy v) | v == a = at
                   | otherwise = TyVarTy v



bkArrow = go [] [] 
  where 
    go vs ts (ForAllTy v t) = go (v:vs) ts t 
    go vs ts (FunTy tx t)   = go vs (tx:ts) t 
    go vs ts _              = (reverse vs, reverse ts) 

sep _ [] = []
sep _ [x] = x 
sep c (x:xs) = x ++ c ++ sep c xs 


instance Show CoreExpr where
  show = showPpr 
instance Show Type where
  show = showPpr 

-- NV HERE: How do we combine proofs?
combineProofs :: CoreExpr -> [CoreExpr] -> CoreExpr
combineProofs _ (x:_) = x 
combineProofs e []  =  e

