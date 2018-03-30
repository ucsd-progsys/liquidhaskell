{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module ListFunctors where

import Prelude hiding (fmap, id, Maybe(..))

import Language.Haskell.Liquid.ProofCombinators

-- | Functor Laws :
-- | fmap-id fmap id ≡ id
-- | fmap-distrib ∀ g h . fmap (g ◦ h) ≡ fmap g ◦ fmap h



{-@ reflect fmap @-}
fmap :: (a -> b) -> Maybe a -> Maybe b
fmap f Nothing  = Nothing
fmap f (Just x) = Just (f x)

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)


{-@ fmap_id :: xs:Maybe a -> { fmap id xs == id xs } @-}
fmap_id :: Maybe a -> Proof
fmap_id Nothing  = trivial 
fmap_id (Just _) = trivial


-- | Distribution


{-@ fmap_distrib :: f:(b -> c) -> g:(a -> b) -> xs:Maybe a
               -> { fmap  (compose f g) xs == (compose (fmap f) (fmap g)) (xs) } @-}
fmap_distrib :: (b -> c) -> (a -> b) -> Maybe a -> Proof
fmap_distrib _ _ Nothing  = trivial 
fmap_distrib f g (Just x) = trivial

data Maybe a = Nothing | Just a
{-@ data Maybe a = Nothing | Just a @-}
