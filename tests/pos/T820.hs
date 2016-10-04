{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--higherorder"        @-}
module Data.Foo where

import Language.Haskell.Liquid.ProofCombinators 

{-@ data Foo = Foo { foox :: (Int -> Int) , fooy :: Int } @-}
data Foo = Foo { x :: Int -> Int , y :: Int }



{-@ data VerifiedEq a = VerifiedEq {
      eq :: a -> a -> Bool
    , refl :: x:a -> { v:() | Prop (eq x x) }
    , sym :: x:a -> y:a -> { v:() | Prop (eq x y) ==> Prop (eq y x) }
    , trans :: x:a -> y:a -> z:a -> { v:() | Prop (eq x y) && Prop (eq y z) ==> Prop (eq x z) }
    }
@-}
data VerifiedEq a = VerifiedEq {
    eq :: a -> a -> Bool
  , refl :: a -> Proof
  , sym :: a -> a -> Proof
  , trans :: a -> a -> a -> Proof
  }

{-@ data VerifiedOrd a = VerifiedOrd {
      leq :: (a -> a -> Bool)
    , total :: (x:a -> y:a -> { Prop (leq x y) || Prop (leq y x) })
    , antisym :: (x:a -> y:a -> { Prop (leq x y) || Prop (leq y x) ==> x == y })
    , trans2 :: (x:a -> y:a -> z:a -> { Prop (leq x y) && Prop (leq y z) ==> Prop (leq x z) })
    , verifiedEq :: VerifiedEq a
    }
@-}


data VerifiedOrd a = VerifiedOrd {
    leq :: a -> a -> Bool
  , total :: a -> a -> Proof
  , antisym :: a -> a -> Proof
  , trans2 :: a -> a -> a -> Proof
  , verifiedEq :: VerifiedEq a
  }

