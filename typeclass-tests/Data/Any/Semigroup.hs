{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--aux-inline" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Any.Semigroup where
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
import Data.Any
import Data.List.NonEmpty
import Data.List


instance Semigroup Any where --
  mappend (Any b) (Any b') = Any $ b || b'
  sconcat (NonEmpty h t) = foldlList mappend h t

instance VSemigroup Any where
  lawAssociative _ _ _ = ()
  lawSconcat _ = ()

instance Monoid Any where
  mempty = Any False
  mconcat = foldrList mappend mempty

instance VMonoid Any where
  lawMconcat _ = ()
  lawEmpty _ = ()
