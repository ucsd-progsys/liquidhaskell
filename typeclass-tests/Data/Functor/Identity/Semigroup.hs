{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--aux-inline" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Functor.Identity.Functor where
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
import Data.Function
import Data.Functor.Identity
import Data.List
import Data.List.NonEmpty
import Data.Semigroup.Classes

instance Semigroup a => Semigroup (Identity a) where
  mappend (Identity v) (Identity v') = Identity (mappend v v')
  sconcat (NonEmpty h t) = foldlList mappend h t

instance Monoid a => Monoid (Identity a) where
  mempty = Identity mempty
  mconcat xs = foldrList mappend mempty xs

instance VSemigroup a => VSemigroup (Identity a) where
  lawAssociative (Identity v) (Identity v') (Identity v'') = lawAssociative v v' v''
  lawSconcat (NonEmpty h t) = sconcat (NonEmpty h t) `cast` ()

instance VMonoid a => VMonoid (Identity a) where
  lawEmpty (Identity v) = lawEmpty v
  lawMconcat xs = mconcat xs `cast` ()

