{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module FunctorList where

import Prelude hiding (fmap, id)

import Language.Haskell.Liquid.ProofCombinators

-- | Functor Laws :
-- | fmap-id fmap id ≡ id
-- | fmap-distrib ∀ g h . fmap (g ◦ h) ≡ fmap g ◦ fmap h

{-@ data Identity a = Identity { runIdentity :: a } @-}
data Identity a = Identity a


{-@ reflect fmap @-}
fmap :: (a -> b) -> Identity a -> Identity b
fmap f (Identity x) = Identity (f x)

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ fmap_id :: xs:Identity a -> { fmap id xs == id xs } @-}
fmap_id :: Identity a -> Proof
fmap_id (Identity x)
  =   trivial 

{-@ fmap_distrib :: f:(a -> a) -> g:(a -> a) -> xs:Identity a
               -> { fmap  (compose f g) xs == (compose (fmap f) (fmap g)) (xs) } @-}
fmap_distrib :: (a -> a) -> (a -> a) -> Identity a -> Proof
fmap_distrib f g (Identity x)
  =   trivial 
