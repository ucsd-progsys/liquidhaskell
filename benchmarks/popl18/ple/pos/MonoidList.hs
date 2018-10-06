{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module MonoidList where

import Prelude hiding (mappend, mempty)

import Language.Haskell.Liquid.ProofCombinators

-- | Monoid
-- | mempty-left ∀ x . mappend mempty  x ≡ x
-- | mempty-right ∀ x . mappend x  mempty ≡ x
-- | mappend-assoc ∀ x y z . mappend (mappend x  y) z ≡ mappend x (mappend y z)

{-@ axiomatize mappend @-}
mappend :: L a -> L a -> L a
mappend Emp      ys = ys
mappend (x :::xs) ys = x ::: mappend xs ys

{-@ axiomatize mempty @-}
mempty :: L a
mempty = Emp

mempty_left :: L a -> Proof
{-@ mempty_left :: x:L a -> { mappend mempty x == x }  @-}
mempty_left xs
  =   trivial 

mempty_right :: L a -> Proof
{-@ mempty_right :: x:L a -> { mappend x mempty == x}  @-}
mempty_right Emp
  = trivial 

mempty_right (x ::: xs)
  =   mempty_right xs

{-@ mappend_assoc :: xs:L a -> ys:L a -> zs:L a
               -> {mappend (mappend xs ys) zs == mappend xs (mappend ys zs) } @-}
mappend_assoc :: L a -> L a -> L a -> Proof
mappend_assoc Emp ys zs
  =   trivial 

mappend_assoc (x ::: xs) ys zs
  =   mappend_assoc xs ys zs

data L a = Emp | a ::: L a
{- data L [llen] a = Emp | (:::) {x::a, xs:: (L a)} @-}

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen Emp        = 0
llen (_ ::: xs) = 1 + llen xs
