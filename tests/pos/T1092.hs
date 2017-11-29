{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
module VerifiedEqInstances where

import Language.Haskell.Liquid.ProofCombinators

{-@ data VerifiedEq a = VEQ {
      eq :: a -> a -> Bool
    , refl :: x:a -> { v:() | eq x x }
    , sym :: x:a -> y:a -> { v:() | eq x y ==> eq y x }
    , trans :: x:a -> y:a -> z:a -> { v:() | eq x y && eq y z ==> eq x z }
    }
@-}
data VerifiedEq a = VEQ {
    eq    :: a -> a -> Bool
  , refl  :: a -> Proof
  , sym   :: a -> a -> Proof
  , trans :: a -> a -> a -> Proof
  }

{-@ axiomatize eqInt @-}
eqInt :: Int -> Int -> Bool
eqInt x y = x == y
{-# INLINE eqInt #-}

{-@ eqIntRefl :: x:Int -> { eqInt x x } @-}
eqIntRefl :: Int -> Proof
eqIntRefl x = eqInt x x ==. x == x *** QED

{-@ eqIntSym :: x:Int -> y:Int -> { eqInt x y ==> eqInt y x } @-}
eqIntSym :: Int -> Int -> Proof
eqIntSym x y = eqInt x y ==. x == y ==. y == x *** QED

{-@ eqIntTrans :: x:Int -> y:Int -> z:Int -> { eqInt x y && eqInt y z ==> eqInt x z } @-}
eqIntTrans :: Int -> Int -> Int -> Proof
eqIntTrans x y z = (eqInt x y && eqInt y z) ==. (x == y && y == z) ==. x == z *** QED

veqInt :: VerifiedEq Int
veqInt = VEQ eqInt eqIntRefl eqIntSym eqIntTrans

{-@ axiomatize eqDouble @-}
eqDouble :: Double -> Double -> Bool
eqDouble x y = x == y
{-# INLINE eqDouble #-}

{-@ eqDoubleRefl :: x:Double -> { eqDouble x x } @-}
eqDoubleRefl :: Double -> Proof
eqDoubleRefl x = eqDouble x x ==. x == x *** QED

{-@ eqDoubleSym :: x:Double -> y:Double
                -> { eqDouble x y ==> eqDouble y x } @-}
eqDoubleSym :: Double -> Double -> Proof
eqDoubleSym x y = eqDouble x y ==. x == y ==. y == x *** QED

{-@ eqDoubleTrans :: x:Double -> y:Double -> z:Double
                  -> { eqDouble x y && eqDouble y z ==> eqDouble x z } @-}
eqDoubleTrans :: Double -> Double -> Double -> Proof
eqDoubleTrans x y z
  =   (eqDouble x y && eqDouble y z)
  ==. (x == y       && y == z)
  ==. x == z
  *** QED

veqDouble :: VerifiedEq Double
veqDouble = VEQ eqDouble eqDoubleRefl eqDoubleSym eqDoubleTrans
