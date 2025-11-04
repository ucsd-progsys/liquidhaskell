{-# LANGUAGE GADTs #-}
{-@ LIQUID "--expect-error-containing=The constructor StratRecOccNotSmall.VArr of the type StratRecOccNotSmall.Val was declared stratified but it has a recursive occurence whose index StratRecOccNotSmall.Val (StratRecOccNotSmall.TArr t1 t2) is not smaller than the return index StratRecOccNotSmall.Val (StratRecOccNotSmall.TArr t1 t2)" @-}
module StratRecOccNotSmall where

import Language.Haskell.Liquid.ProofCombinators

data Ty = TInt | TArr Ty Ty

{-@ stratified Val @-}
data Val where
  {-@ VInt :: Int -> Prop (Val TInt) @-}
  VInt :: Int -> Val
  {-@ VArr :: t1:Ty -> t2:Ty -> (Prop (Val (TArr t1 t2)) -> Prop (Val t2)) -> Prop (Val (TArr t1 t2)) @-}
  VArr :: Ty -> Ty -> (Val -> Val) -> Val
data VAL = Val Ty
