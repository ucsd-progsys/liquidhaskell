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

decrType :: Var -> SpecType -> [Var] -> [(F.Symbol, SpecType)] -> SpecType
decrType x ti xs xts = {- F.tracepp ("Decr type for " ++ showpp x ++ " on arguments " ++ showpp xs) $ -} go [] [] xs ti 
  where
    go accvs accxts (v:vs) (RFun x tx t r) 
      | isDecreasing mempty mempty tx  = let (x', tx') = R.makeDecrType mempty (zip (v:accvs) ((x,tx):accxts)) 
                                         in RFun x' tx' t r 
    go accvs accxts (v:vs) (RFun x tx t r) = RFun x tx (go (v:accvs) ((x,tx):accxts) vs t) r
    go accvs accxts (v:vs) (RAllT a t) = RAllT a $ go accvs accxts vs t
    go _     _       _     t = t 
