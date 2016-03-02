{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExtendedDefaultRules #-}


{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
module Append where

import Axiomatize
import Equational
import Prelude hiding (return, (>>=))


data L a = N 

-- | Definition of the list monad

{-@ axiomatize return @-}
$(axiomatize
  [d| return :: a -> L a
      return x = N
    |])

{-@ axiomatize append @-}
$(axiomatize
  [d| append :: L a -> L a -> L a
      append N ys        = ys
    |])

{-@ axiomatize bind @-}
$(axiomatize
  [d| bind :: L a -> (a -> L a) -> L a
      bind N        f = N
    |])


-- | Right Identity m >>= return ≡  m
{-@ prop_right_identity :: Eq a => L a -> {v:Proof | bind N return == N } @-}
prop_right_identity :: Eq a => L a -> Proof
prop_right_identity N =  refl (bind N return) `by` pr1 
  where
    e1  = bind N return
    pr1 = axiom_bind_N return
    e2  = N



-- | List definition


instance Eq a => Eq (L a) where
  N == N                 = True

{-@ data L [llen] @-}
{-@ invariant {v: L a | llen v >= 0} @-}

{-@ measure llen @-}
llen :: L a -> Int
llen N = 0
