{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--aux-inline" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.List.Semigroup where
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
import Data.List.NonEmpty
import Data.List


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
