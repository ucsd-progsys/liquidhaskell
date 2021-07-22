{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--aux-inline" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Dual.Semigroup where
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
import Data.Dual
import Data.Semigroup.Classes
import Data.List.NonEmpty
import Data.List
import Data.Endo
import Data.Function

instance Semigroup (Endo a) where
  mappend (Endo f) (Endo g) = Endo (compose f g)
  sconcat (NonEmpty h t) = foldlList mappend h t


instance VSemigroup (Endo a) where
  lawAssociative (Endo f) (Endo g) (Endo h) = composeAssoc f g h `cast` ()
  lawSconcat (NonEmpty h t) = sconcat (NonEmpty h t) `cast` ()

instance Monoid (Endo a) where
  mempty = Endo id
  mconcat = foldrList mappend mempty

instance VMonoid (Endo a) where
  lawEmpty (Endo f) = composeId f
  lawMconcat _ = ()

