{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Constraint.ProofToCore where

import CoreSyn hiding (Expr, Var)
import qualified CoreSyn as H

import Var hiding (Var)
import CoreUtils 

import Type hiding (Var)
import TypeRep 

import Language.Haskell.Liquid.GhcMisc 
import Language.Haskell.Liquid.WiredIn 

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

type CmbExpr = CoreExpr -> CoreExpr -> CoreExpr

class ToCore a where
  toCore :: CmbExpr -> CoreExpr -> a -> CoreExpr 

instance ToCore HInstance where
  toCore c e i = mkApp (toCore c e $ inst_axiom i) (toCore c e <$> inst_args i) 

instance ToCore HProof where
  toCore _ e Invalid = e
  toCore c e p       = combineProofs c e $ (toCore c e <$> p_evidence p)

instance ToCore HAxiom where
  toCore c e a = toCore c e $ axiom_name a 
 
instance ToCore HExpr  where
  toCore c e (EVar v)    = toCore c e v 
  toCore c' e (EApp c es) = mkApp (toCore c' e c) (toCore c' e <$> es) 

instance ToCore HCtor where
  toCore c' e c =  toCore c' e $ ctor_var c 

instance ToCore HVar where
  toCore _ _ v = H.Var $ var_info v 

mkApp f es = foldl (flip Let) (foldl App f' (reverse es')) (reverse  bs)  
  where
   vts = resolveVs $ zip ts (exprType <$> es)
   (as, ts)  = bkArrow (exprType f)
   f' = instantiateVars vts f 
   ds = makeDictionaries dictionaryVar f' 
   (bs, es', _) = foldl anf ([], [], [1..]) (ds ++ (instantiateVars vts <$> es))

anf :: ([CoreBind], [CoreExpr], [Int]) -> CoreExpr -> ([CoreBind], [CoreExpr], [Int])
anf (bs, es, i:uniq) (App f e) = ((NonRec v (App f e')):(bs++bs'), H.Var v:es, uniq')
  where v = stringVar ("proof_anf" ++ show i) (exprType $ App f e)
        (bs', [e'], uniq') = anf ([], [], uniq) e

anf (bs, es, uniq) e = (bs, e:es, uniq)  

instantiateVars vts e = go e (exprType e)
  where
    go :: CoreExpr -> Type -> CoreExpr
    go e (ForAllTy a t) = go (App e (Type $ fromMaybe (TyVarTy a) $ L.lookup a vts)) t  
    go e _ = e 

makeDictionaries dname e = go (exprType e)
  where
    go (ForAllTy _ t) = go t 
    go (FunTy tx t  ) | isClassPred tx = (makeDictionary dname tx):go t
    go _              = []


makeDictionary dname t = App (H.Var dname) (Type t) 

showPair (v, TyVarTy t) = show (tvId v) ++ " : " ++ show (tvId t) 
showPair (v, t) = show (tvId v) ++ " : " ++ show t 

showTy (ForAllTy a t) = "forall " ++ show (tvId a) ++ " . " ++ showTy t 
showTy (TyVarTy a)    = show (tvId a)
showTy (FunTy t1 t2)  = showTy t1 ++ " -> " ++ showTy t2  
showTy (TyConApp c ts)  = show c ++ sep " " (showTy <$> ts) 
showTy t = show t 


resolveVs :: [(Type, Type)] -> [(Id, Type)]
resolveVs [] = []
resolveVs ((ForAllTy a t1, t2)     :ts) = resolveVs ((t1, t2):ts)
resolveVs ((t1, ForAllTy a t2)     :ts) = resolveVs ((t1, t2):ts)
resolveVs ((FunTy   t1 t2, FunTy t1' t2'):ts) = resolveVs ((t1, t1'):(t2, t2'):ts)
resolveVs ((AppTy t1 t2, AppTy t1' t2'):ts) = resolveVs ((t1, t1'):(t2, t2'):ts)
resolveVs ((TyVarTy a, TyVarTy a'):ts) | a == a' = resolveVs ts 
resolveVs ((TyVarTy a, t):ts)               = let vts = (resolveVs (substTyV (a, t) <$> ts)) in (a, resolveVar a t vts) : vts 
resolveVs ((t, TyVarTy a):ts)               = let vts = (resolveVs (substTyV (a, t) <$> ts)) in (a, resolveVar a t vts) : vts 
resolveVs ((TyConApp _ cts,TyConApp _ cts'):ts) = resolveVs (zip cts cts' ++ ts)
resolveVs ((LitTy _, LitTy _):ts) = resolveVs ts 
resolveVs (tt:ts) = error $ showPpr tt




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



combineProofs :: CmbExpr -> CoreExpr -> [CoreExpr] -> CoreExpr
combineProofs _ e []  =  e
combineProofs c _ es = foldl (flip Let) (combine [1..] c (H.Var v) (H.Var <$> vs)) (bs ++ [dictionaryBind]) 
    where 
      (v:vs, bs) = unzip [let v = (stringVar ("proof_anf_bind" ++ show i) (exprType e)) in (v, NonRec v e) 
                              | (e, i) <- zip es [1..] ]

combine _ c e []             = e
combine _ c e' [e]           = c e' e
combine (i:uniq) c e' (e:es) = Let (NonRec v (c e' e)) (combine uniq c (H.Var v) es)
  where
  	v = stringVar ("proof_anf_cmb" ++ show i) (exprType $ c e' e)
