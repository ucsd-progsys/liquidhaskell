{-# LANGUAGE GADTs #-}
{-@ LIQUID "--expect-error-containing=The constructor StratNoPropRet.VArr of the type StratNoPropRet.Val was declared stratified but it does not return an indexed type, instead it returns StratNoPropRet.Val" @-}
module StratNoPropRet where

import Language.Haskell.Liquid.ProofCombinators

data Ty = TInt | TArr Ty Ty

{-@ stratified Val @-}
data Val where
  {-@ VInt :: Int -> Prop (Val TInt) @-}
  VInt :: Int -> Val
  {-@ VArr :: t1:Ty -> t2:Ty -> (Prop (Val t1) -> Prop (Val t2)) -> Val @-}
  VArr :: Ty -> Ty -> (Val -> Val) -> Val
data VAL = Val Ty
