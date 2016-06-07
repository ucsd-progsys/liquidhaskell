{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorderqs" @-}



{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module FunctorList where

import Prelude hiding (fmap, id)

import Proves
import Helper

-- | Functor Laws :
-- | fmap-id fmap id ≡ id
-- | fmap-distrib ∀ g h . fmap (g ◦ h) ≡ fmap g ◦ fmap h

{-@ data Identity a = Identity { runIdentity :: a } @-}
data Identity a = Identity a


{-@ axiomatize fmap @-}
fmap :: (a -> b) -> Identity a -> Identity b
fmap f (Identity x) = Identity (f x)

{-@ axiomatize id @-}
id :: a -> a
id x = x

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ fmap_id :: xs:Identity a -> { fmap id xs == id xs } @-}
fmap_id :: Identity a -> Proof
fmap_id (Identity x)
  =   fmap id (Identity x)
  ==! Identity (id x)
  ==! Identity x
  ==! id (Identity x)
  *** QED


{-@ fmap_distrib :: f:(a -> a) -> g:(a -> a) -> xs:Identity a
               -> { fmap  (compose f g) xs == (compose (fmap f) (fmap g)) (xs) } @-}
fmap_distrib :: (a -> a) -> (a -> a) -> Identity a -> Proof
fmap_distrib f g (Identity x)
  =   fmap (compose f g) (Identity x)
  ==! Identity ((compose f g) x)
  ==! Identity (f (g x))
  ==! fmap f (Identity (g x))
  ==! (fmap f) (fmap g (Identity x))
  ==! (compose (fmap f) (fmap g)) (Identity x)
  *** QED 
