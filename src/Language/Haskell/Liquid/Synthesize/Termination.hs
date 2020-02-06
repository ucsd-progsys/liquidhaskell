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
decrType _x ti xs _xts = -- F.tracepp ("Decr type for " ++ showpp x ++ " on arguments " ++ showpp xs) $ 
  go xs ti 
  where
    go (v:vs) (RFun x tx t r) 
      | isDecreasing mempty mempty tx  = let Left (x', tx') = R.makeDecrType mempty [(v,(x,tx))] 
                                         in  RFun x' tx' t r 
    go (v:vs) (RFun x tx t r) = RFun x tx (go vs t) r
    go vs (RAllT a t x) = RAllT a (go vs t) x
    go _     t = t 
