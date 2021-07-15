{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--aux-inline" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.All.Semigroup where
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
import Data.All
import Data.List.NonEmpty
import Data.List
-- import Data.List.Functor


instance Semigroup All where --
  mappend (All b) (All b') = All $ b && b'
  sconcat (NonEmpty h t) = foldlList mappend h t

instance VSemigroup All where
  lawAssociative _ _ _ = ()
  lawSconcat _ = ()

instance Monoid All where
  mempty = All True
  mconcat = foldrList mappend mempty

instance VMonoid All where
  lawMconcat _ = ()
  lawEmpty _ = ()
