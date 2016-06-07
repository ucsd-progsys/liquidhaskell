{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--extensionality"  @-}



{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module FunctorList where

import Prelude hiding (fmap, id)

import Proves
import Helper

-- | Functor Laws :
-- | fmap-id fmap id ≡ id
-- | fmap-distrib ∀ g h . fmap (g ◦ h) ≡ fmap g ◦ fmap h

{-@ data Reader r a = Reader { runIdentity :: r -> a } @-}
data Reader r a     = Reader { runIdentity :: r -> a }


{-@ axiomatize fmap @-}
fmap :: (a -> b) -> Reader r a -> Reader r b
fmap f (Reader rd) = Reader (\r -> f (rd r))

{-@ axiomatize id @-}
id :: a -> a
id x = x

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ fmap_id :: xs:Reader r a -> { fmap id xs == id xs } @-}
fmap_id :: Reader r a -> Proof
fmap_id (Reader x)
   =   fmap id (Reader x)
   ==! Reader (\r -> id (x r))
   ==! Reader (\r -> x r)
   ==! Reader x
   ==! id (Reader x)
   *** QED

{-@ fmap_distrib :: f:(a -> a) -> g:(a -> a) -> xs:Reader r a
               -> { fmap  (compose f g) xs == (compose (fmap f) (fmap g)) (xs) } @-}
fmap_distrib :: (a -> a) -> (a -> a) -> Reader r a -> Proof
fmap_distrib f g (Reader x)
  =   fmap (compose f g) (Reader x)
  ==! Reader (\r -> (compose f g) (x r))
  ==! Reader (\r -> f ( g (x r)))
  ==! Reader (\r -> f ((\w -> g (x w)) r))
  ==! fmap f (Reader (\w -> g (x w)))
  ==! fmap f (fmap g (Reader x))
  ==! (compose (fmap f) (fmap g)) (Reader x)
  *** QED
