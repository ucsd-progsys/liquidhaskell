{-@ LIQUID "--expect-error-containing=The constructor Test.VArr of the type Test.Val was declared stratified but it does not return a Prop type, instead it returns Test.Val" @-}
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
