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
-- compose :: (a -> a) -> (a -> a) -> a -> a
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


{-@ composition1 :: x:{Maybe (a -> a) | is_Just x }
                -> y:Maybe (a -> a)
                -> z:Maybe a
                -> {v:Proof | Just ((from_Just x) ((from_Just y) (from_Just z))) ==
                  Just (from_Just x (from_Just y (from_Just z)))
                  } @-}
composition1 :: Maybe (a -> a) -> Maybe (a -> a) -> Maybe a -> Proof
composition1 x y z
  = toProof (
               Just ((from_Just x) ((from_Just y) (from_Just z)))
             ==! Just (from_Just x (from_Just y (from_Just z)))
            )
{-@ composition0 :: x:{Maybe (a -> a) | is_Just x }
                -> y:Maybe (a -> a)
                -> z:Maybe a
                -> {v:Proof | seq (seq (seq (pure compose) x) y) z ==
                  Just ((from_Just x) ((from_Just y) (from_Just z)))
                  } @-}
composition0 :: Maybe (a -> a) -> Maybe (a -> a) -> Maybe a -> Proof
composition0 x y z
  = toProof (
               seq (seq (seq (pure compose) x) y) z
             ==! seq (seq (seq (Just compose) x) y) z
             ==! seq (seq (Just (compose (from_Just x))) y) z
             ==! seq (Just (compose (from_Just x) (from_Just y))) z
             ==! Just ((compose (from_Just x) (from_Just y)) (from_Just z))
             ==! Just ((from_Just x) ((from_Just y) (from_Just z)))
             ==! Just (from_Just x (from_Just y (from_Just z)))
            )

{-

seq (seq (seq (pure compose) x) y) z
  ==! seq (seq (seq (Just compose) x) y) z
  ==! seq (seq (Just (compose (from_Just x))) y) z
  ==! seq (Just (compose (from_Just x) (from_Just y))) z
  ==! Just ((compose (from_Just x) (from_Just y)) (from_Just z))
  ==! Just ((from_Just x) ((from_Just y) (from_Just z)))
  ==! Just (from_Just x (from_Just y (from_Just z)))
  ==! Just (from_Just x (from_Just (Just (from_Just y (from_Just z)))))
  ==! Just (from_Just x (from_Just (seq y z)))
  ==! seq x (seq y z)

-}





bar :: Maybe (a -> a) ->  a ->  a
{-@ bar :: x:Maybe (a -> a) -> z: a
        -> {v: a | v == from_Just x z }
  @-}
bar x z = from_Just x z


{-
{- composition :: x:Maybe (a -> a)
                -> y:Maybe (a -> a)
                -> z:Maybe a
                -> {v:Proof | (seq (seq (seq (pure compose) x) y) z) = seq x (seq y z) } @-}
composition :: Maybe (a -> a) -> Maybe (a -> a) -> Maybe a -> Proof
composition x y z
   | is_Nothing x || is_Nothing y || is_Nothing z
   = toProof $
      seq (seq (seq (pure compose) x) y) z
        ==! Nothing
        ==! seq x (seq y z)
composition x y z
  = toProof $
      seq (seq (seq (pure compose) x) y) z
        ==! seq (seq (seq (Just compose) x) y) z
        ==! seq (seq (Just (compose (from_Just x))) y) z
        ==! seq (Just (compose (from_Just x) (from_Just y))) z
        ==! Just ((compose (from_Just x) (from_Just y)) (from_Just z))
        ==! Just ((from_Just x) ((from_Just y) (from_Just z)))
        ==! Just (from_Just x (from_Just y (from_Just z)))
        ==! Just (from_Just x (from_Just (Just (from_Just y (from_Just z)))))
        ==! Just (from_Just x (from_Just (seq y z)))
        ==! seq x (seq y z)

-}
data Maybe a = Nothing | Just a

{-@ measure from_Just @-}
from_Just :: Maybe a -> a
{-@ from_Just :: xs:{Maybe a | is_Just xs } -> {v:a  | v == from_Just xs}@-}
from_Just (Just x) = x

{-@ measure is_Nothing @-}
is_Nothing :: Maybe a -> Bool
is_Nothing Nothing = True
is_Nothing _       = False

{-@ measure is_Just @-}
is_Just :: Maybe a -> Bool
is_Just (Just _) = True
is_Just _        = False
