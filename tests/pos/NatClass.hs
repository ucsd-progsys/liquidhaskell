{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}

module Nat where

import Language.Haskell.Liquid.ProofCombinators

{-@ data N [toInt] = Zero | Suc N @-}
data N = Zero | Suc N

{-@ measure toInt @-}
{-@ toInt :: N -> Nat @-}
toInt :: N -> Int
toInt Zero = 0
toInt (Suc n) = 1 + toInt n


{-@ class (Eq a) => VerifiedEq a where
      eq :: a -> a -> Bool
      refl :: x:a -> { v:() | Prop (eq x x) }
@-}
class (Eq a) => VerifiedEq a where
  eq :: a -> a -> Bool
  refl :: a -> Proof


{-@ axiomatize eqN @-}
eqN :: N -> N -> Bool
eqN Zero Zero = True
eqN (Suc m) (Suc n) = eqN m n
eqN _ _ = False

{-@ eqNRefl :: x:N -> { eqN x x } @-}
eqNRefl :: N -> Proof
eqNRefl Zero =   eqN Zero Zero
             ==. True
             *** QED
eqNRefl (Suc n) =   eqN (Suc n) (Suc n)
                ==. eqN n n
                ==. True ? eqNRefl n
                *** QED

instance Eq N where
  (==) = eqN

instance VerifiedEq N where
  {-@ define $ceq = eqN @-}
  eq x y   = eqN x y 
  refl  = eqNRefl
