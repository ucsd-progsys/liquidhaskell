{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorderqs" @-}



{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module ListFunctors where

import Prelude hiding (fmap, id, Maybe(..))

import Proves
import Helper

-- | Functor Laws :
-- | fmap-id fmap id ≡ id
-- | fmap-distrib ∀ g h . fmap (g ◦ h) ≡ fmap g ◦ fmap h



{-@ axiomatize fmap @-}
fmap :: (a -> b) -> Maybe a -> Maybe b
fmap f Nothing  = Nothing
fmap f (Just x) = Just (f x)

{-@ axiomatize id @-}
id :: a -> a
id x = x

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{- fmap_id' :: {v:Proof | fmap id == id } @-}
{-
fmap_id' :: Proof
fmap_id' = abstract (fmap id) id fmap_id
-}

{-@ fmap_id :: xs:Maybe a -> { fmap id xs == id xs } @-}
fmap_id :: Maybe a -> Proof
fmap_id Nothing
  =   fmap id Nothing
  ==! Nothing
  ==! id Nothing
  *** QED
fmap_id (Just x)
  = fmap id (Just x)
  ==! Just (id x)
  ==! Just x
  ==! id (Just x)
  *** QED


-- | Distribution

{- fmap_distrib' :: f:(a -> a) -> g:(a -> a)
               -> {v:Proof | fmap  (compose f g) == compose (fmap f) (fmap g) } @-}
{-
fmap_distrib' :: (a -> a) -> (a -> a) -> Proof
fmap_distrib' f g
  = abstract (fmap  (compose f g)) (compose (fmap f) (fmap g))
       (fmap_distrib f g)
-}

{-@ fmap_distrib :: f:(a -> a) -> g:(a -> a) -> xs:Maybe a
               -> { fmap  (compose f g) xs == (compose (fmap f) (fmap g)) (xs) } @-}
fmap_distrib :: (a -> a) -> (a -> a) -> Maybe a -> Proof
fmap_distrib f g Nothing
  = 
      (compose (fmap f) (fmap g)) Nothing
        ==! (fmap f) ((fmap g) Nothing)
        ==! fmap f (fmap g Nothing)
        ==! fmap f Nothing
        ==! Nothing
        ==! fmap (compose f g) Nothing
        *** QED
fmap_distrib f g (Just x)
  =        fmap (compose f g) (Just x)
       ==! Just ((compose f g) x)
       ==! Just (f (g x))
       ==! (fmap f) (Just (g x))
       ==! (fmap f) (fmap g (Just x))
       ==! (fmap f) ((fmap g) (Just x))
       ==! (compose (fmap f) (fmap g)) (Just x)
       *** QED

data Maybe a = Nothing | Just a
{-@ data Maybe a = Nothing | Just a @-}
