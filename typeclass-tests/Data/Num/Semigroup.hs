{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--aux-inline" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Num.Semigroup where
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

data Sum a = Sum {getSum :: a}

instance Num a => Semigroup (Sum a) where
  mappend (Sum x) (Sum y) = Sum $ x + y
  sconcat (NonEmpty h t) = foldlList mappend h t

instance Num a => VSemigroup (Sum a) where
  lawAssociative _ _ _ = ()
  lawSconcat _ = ()

instance Num a => Monoid (Sum a) where
  mempty = Sum 0
  mconcat = foldrList mappend mempty

data Product a = Product {getProduct :: a}

instance Num a => Semigroup (Product a) where
  mappend (Product x) (Product y) = Product $ x * y
  sconcat (NonEmpty h t) = foldlList mappend h t

instance Num a => VSemigroup (Product a) where
  lawAssociative _ _ _ = ()
  lawSconcat _ = ()

instance Num a => Monoid (Product a) where
  mempty = Product 1
  mconcat = foldlList mappend mempty

