{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Constraint.ProofToCore where

import CoreSyn hiding (Expr, Var)
import qualified CoreSyn as H

import Var hiding (Var)
import CoreUtils 

import Type hiding (Var)

import Language.Fixpoint.Misc (traceShow)

import Language.Haskell.Liquid.GhcMisc 

import Prover.Types 

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

mkApp f es = traceShow ("\n\nmkApp " ++ show (exprType f) ++ "\n\nARGS \n\n" ++ (sep "\n" (show . exprType <$> es))) $ foldl App f es 
  -- HERE type variables and dictionaries should be instantiated somehow...


sep _ [] = []
sep _ [x] = x 
sep c (x:xs) = x ++ c ++ sep c xs 


instance Show CoreExpr where
  show = showPpr 
instance Show Type where
  show = showPpr 


combineProofs :: CoreExpr -> [CoreExpr] -> CoreExpr
combineProofs _ (x:_) = x 
combineProofs e []  =  e

