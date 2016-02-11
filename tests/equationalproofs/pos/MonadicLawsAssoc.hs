
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExtendedDefaultRules #-}

{-@ LIQUID "--higherorder"      @-}
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

-- | Left Associativity: (m >>= f) >>= g ≡  m >>= (\x -> f x >>= g)


prop_left_assoc :: Eq a => L a -> (a -> L a) -> (a -> L a) -> Proof
{-@ prop_left_assoc :: m: L a -> f:(a -> L a) -> g:(a -> L a) -> Proof @-}
prop_left_assoc m f g 
  = auto 2 ((m `bind` f) `bind` g == m `bind` (\x -> f x `bind` g))

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
