{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--eliminate" @-}
{-@ LIQUID "--maxparams=10"  @-}
{-@ LIQUID "--higherorderqs" @-}



{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module ListFunctors where

import Prelude hiding (fmap, id, Maybe(..), seq, pure)

import Proves
import Helper

-- | Applicative Laws :
-- | identity      pure id <*> v = v
-- | composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-- | homomorphism  pure f <*> pure x = pure (f x)
-- | interchange   u <*> pure y = pure ($ y) <*> u


{-@ axiomatize pure @-}
pure :: a -> Maybe a
pure x = Just x

{-@ axiomatize seq @-}
seq :: Maybe (a -> b) -> Maybe a -> Maybe b
seq f x
  | is_Just f, is_Just x = Just (from_Just f (from_Just x))
  | otherwise            = Nothing


{-@ axiomatize fmap @-}
fmap :: (a -> b) -> Maybe a -> Maybe b
fmap f x
  | is_Just x  = Just (f (from_Just x))
  | otherwise = Nothing

{-@ axiomatize id @-}
id :: a -> a
id x = x

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)


-- | Identity

{-@ identity :: x:Maybe a -> {v:Proof | seq (pure id) x == x } @-}
identity :: Maybe a -> Proof
identity Nothing
  = toProof $
      seq (pure id) Nothing
         ==! Nothing
identity (Just x)
  = toProof $
      seq (pure id) (Just x)
         ==! seq (Just id) (Just x)
         ==! Just (id x)
         ==! Just x


-- | Composition

{- composition :: f:(a -> a) -> g:(a -> a) -> xs:Maybe a
               -> {v:Proof | (seq (seq (seq (pure compose) u) v) w) = seq u (seq v w) } @-}


data Maybe a = Nothing | Just a

{-@ measure from_Just @-}
from_Just :: Maybe a -> a
{-@ from_Just :: xs:{Maybe a | is_Just xs } -> a @-}
from_Just (Just x) = x

{-@ measure is_Nothing @-}
is_Nothing :: Maybe a -> Bool
is_Nothing Nothing = True
is_Nothing _       = False

{-@ measure is_Just @-}
is_Just :: Maybe a -> Bool
is_Just (Just _) = True
is_Just _        = False
