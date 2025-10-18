{-# LANGUAGE GADTs #-}
{-@ LIQUID "--expect-error-containing=The constructor StratNoPropRec.VArr of the type StratNoPropRec.Val was declared stratified but it has a recursive occurence of type StratNoPropRec.Val which is not a Prop type" @-}
module StratNoPropRec where

import Language.Haskell.Liquid.ProofCombinators

data Ty = TInt | TArr Ty Ty

{-@ stratified Val @-}
data Val where
  {-@ VInt :: Int -> Prop (Val TInt) @-}
  VInt :: Int -> Val
  {-@ VArr :: t1:Ty -> t2:Ty -> (Prop (Val t1) -> Val) -> Prop (Val (TArr t1 t2)) @-}
  VArr :: Ty -> Ty -> (Val -> Val) -> Val
data VAL = Val Ty
