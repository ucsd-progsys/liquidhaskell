{-# LANGUAGE GADTs #-}

module StratVal where

import Language.Haskell.Liquid.ProofCombinators

data Ty = TInt | TArr Ty Ty

{-@ stratified Val @-}
data Val where
  {-@ VInt :: Int -> Prop (Val TInt) @-}
  VInt :: Int -> Val
  {-@ VArr :: t1:Ty -> t2:Ty -> (Prop (Val t1) -> Prop (Val t2)) -> Prop (Val (TArr t1 t2)) @-}
  VArr :: Ty -> Ty -> (Val -> Val) -> Val
data VAL = Val Ty
