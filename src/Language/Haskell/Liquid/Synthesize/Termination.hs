{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Synthesize.Termination (
    decrType
  ) where

import           Language.Haskell.Liquid.Types hiding (SVar) 
import qualified Language.Haskell.Liquid.Types.RefType as R

import qualified Language.Fixpoint.Types        as F 


import Var 
import Debug.Trace

decrType :: Var -> SpecType -> [Var] -> [(F.Symbol, SpecType)] -> (SpecType, Bool)
decrType x ti xs xts 
  = F.tracepp ("Decr type for " ++ showpp x ++ " on arguments " ++ showpp xs) 
      $ go [] [] xs ti 
  where
    go accvs accxts (v:vs) (RFun x tx t r) 
      | isDecreasing mempty mempty tx
      , Left (x', tx') <- R.makeDecrType mempty (zip (v:accvs) ((x,tx):accxts)) 
      = (RFun x' tx' t r, True) 

    go accvs accxts (v:vs) (RFun x tx t r) 
      = let (t,b) = go (v:accvs) ((x,tx):accxts) vs t in 
           (RFun x tx t r, b)
    go accvs accxts vs (RAllT a t x) 
      = let (t,b) = go accvs accxts vs t in (RAllT a t x, b)
    go _     _       _     t 
      = (t, False) 
