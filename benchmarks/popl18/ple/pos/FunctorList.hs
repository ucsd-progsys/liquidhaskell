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



{-@ reflect fmap @-}
fmap :: (a -> b) -> L a -> L b
fmap _ N        = N 
fmap f (C x xs) = C (f x) (fmap f xs)

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ fmap_id :: xs:L a -> { fmap id xs == id xs } @-}
fmap_id :: L a -> Proof
fmap_id N
  = trivial 
fmap_id (C x xs)
  = fmap_id (xs)

-- | Distribution

{-@ fmap_distrib :: f:(a -> a) -> g:(a -> a) -> xs:L a
               -> {v:Proof | fmap  (compose f g) xs == (compose (fmap f) (fmap g)) (xs) } @-}
fmap_distrib :: (a -> a) -> (a -> a) -> L a -> Proof
fmap_distrib f g N
  = trivial 
fmap_distrib f g (C x xs)
  = fmap_distrib f g xs


data L a = N | C a (L a)
{-@ data L [llen] a = N | C {lhd :: a, ltl :: L a }  @-}


{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen N        = 0
llen (C _ xs) = 1 + llen xs

