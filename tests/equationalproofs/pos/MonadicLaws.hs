
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExtendedDefaultRules #-}

{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
module Append where

import Axiomatize
import Equational
import Prelude hiding (return, (>>=))


data L a = N |  C a (L a)

-- | Definition of the list monad

{-@ axiomatize return @-}
$(axiomatize
  [d| return :: a -> L a
      return x = C x N
    |])

{-@ axiomatize append @-}
$(axiomatize
  [d| append :: L a -> L a -> L a
      append N ys        = ys
      append (C x xs) ys = C x (append xs ys)
    |])

{-@ axiomatize bind @-}
$(axiomatize
  [d| bind :: L a -> (a -> L a) -> L a
      bind N        f = N
      bind (C x xs) f = append (f x) (xs `bind` f)
    |])


-- NV TODO:
-- 1. remove the manual runFun there
-- 2. check why failure to prove takes so long

-- | Left identity: return a >>= f ≡ f a

prop_left_identity :: Eq a => a -> (a -> L a) -> Proof
{-@ prop_left_identity :: x:a -> f:(a -> L a)
                       -> {v:Proof | bind (return x) f == runFun f x} @-}
prop_left_identity x f = undefined -- auto 2 (bind (return x) f == f x)
  where
    e1  = bind (return x) f
    pr1 = axiom_return x
    e2  = bind (C x N) f
    pr2 = axiom_bind_C f x N
    e3  = append (f x) (bind N f)
    pr3 = axiom_bind_N f
    e4  = append (f x) N
    pr4 = prop_app_nil (f x)
    e5  = f x

-- | Right Identity m >>= return ≡  m
{-@ prop_right_identity :: Eq a => L a -> {v:Proof | bind N return == N } @-}
prop_right_identity :: Eq a => L a -> Proof
prop_right_identity N =  refl (bind N returnZZZ) `by` pr1 -- auto 1 (bind N return == N) --  `by` pr1
  where
    e1  = bind N return
    pr1 = axiom_bind_N returnZZZ
    e2  = N
    returnZZZ = undefined

prop_right_identity (C x xs) = undefined

{-@ f :: x:Int -> {v:Int | v < x} @-}
f :: Int -> Int
f x = x



{-@ prop_app_nil :: ys:L a -> {v:Proof | append ys N == ys} @-}
prop_app_nil :: (Eq a) => L a -> Proof
prop_app_nil N        = auto 1 (append N N        == N     )
prop_app_nil (C x xs) = auto 1 (append (C x xs) N == C x xs)


-- | List definition


instance Eq a => Eq (L a) where
  N == N                 = True
  (C x xs) == (C x' xs') = x == x' && xs == xs'

{-@ data L [llen] @-}
{-@ invariant {v: L a | llen v >= 0} @-}

{-@ measure llen @-}
llen :: L a -> Int
llen N = 0
llen (C x xs) = 1 + llen xs
