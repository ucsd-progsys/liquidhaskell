{-# LANGUAGE RankNTypes #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}
{-@ LIQUID "--aux-inline" @-}
{-@ LIQUID "--ple" @-}

module PNat where

import           Prelude                 hiding ( Semigroup(..)
                                                , Monoid(..)
                                                , foldr
                                                , head
                                                , flip
                                                , tail
                                                , Maybe (..)
                                                , Foldable (..)
                                                )

import SemigroupLib
import Lib

data PNat = Z | S PNat

instance Semigroup PNat where
  mappend Z     n = n
  mappend (S m) n = S (mappend m n)

  sconcat (NonEmpty h t) = foldlList mappend h t

instance VSemigroup PNat where
  lawAssociative Z     _ _ = ()
  lawAssociative (S p) m n = lawAssociative p m n
  lawSconcat (NonEmpty h t) = ()

instance Monoid PNat where
  mempty = Z
  mconcat xs = foldrList mappend mempty xs

instance VMonoid PNat where
  lawEmpty Z     = ()
  lawEmpty (S m) = lawEmpty m
  lawMconcat _ = ()



instance Semigroup (List a) where
  mappend Nil l2 = l2
  mappend (Cons h l1) l2 = Cons h (mappend l1 l2)
  sconcat (NonEmpty h t) = foldlList mappend h t

instance VSemigroup (List a) where
  lawAssociative Nil y z = ()
  lawAssociative (Cons _ x) y z = lawAssociative x y z
  lawSconcat (NonEmpty h t) = ()

instance Monoid (List a) where
  mempty = Nil
  mconcat xs = foldrList mappend mempty xs

instance VMonoid (List a) where
  lawEmpty Nil = ()
  lawEmpty (Cons _ t) = lawEmpty t
  lawMconcat _ = ()
