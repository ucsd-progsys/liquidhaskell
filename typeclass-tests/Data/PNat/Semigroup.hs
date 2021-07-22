{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--aux-inline" @-}
{-@ LIQUID "--typeclass" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.PNat.Semigroup where
import           Prelude                 hiding ( Functor(..)
                                                , Applicative(..)
                                                , Monad(..)
                                                , Foldable(..)
                                                , Maybe(..)
                                                , Monoid(..)
                                                , Semigroup(..)
                                                , Either(..)
                                                , id
                                                , flip
                                                , const
                                                , apply
                                                )
import           Liquid.ProofCombinators
import Data.Semigroup.Classes
import Data.PNat
import Data.List.NonEmpty
import Data.List



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
