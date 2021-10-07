{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--aux-inline" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Maybe.Semigroup where
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
import Data.Maybe
import Data.Semigroup.Classes
import Data.List.NonEmpty
import Data.List


instance Semigroup (First a) where
  First Nothing `mappend` b = b
  a `mappend` _ = a
  sconcat (NonEmpty h t) = foldlList mappend h t

instance VSemigroup (First a) where
  lawAssociative _ _ _ = ()
  lawSconcat _ = ()

instance Monoid (First a) where
  mempty = First Nothing
  mconcat = foldrList mappend mempty

instance VMonoid (First a) where
  lawEmpty (First Nothing) = ()
  lawEmpty _ = ()
  lawMconcat _ = ()


instance Semigroup (Last a) where
  a `mappend` Last Nothing = a
  _ `mappend` b = b
  sconcat (NonEmpty h t) = foldlList mappend h t

instance VSemigroup (Last a) where
  lawAssociative _ _ _ = ()
  lawSconcat _ = ()

instance Monoid (Last a) where
  mempty = Last Nothing
  mconcat = foldrList mappend mempty

instance VMonoid (Last a) where
  lawEmpty (Last Nothing) = ()
  lawEmpty _ = ()
  lawMconcat _ = ()

-- -- Dual First and Last are isomorphic
instance Semigroup a => Semigroup (Maybe a) where
  Nothing `mappend` b = b
  a `mappend` Nothing = a
  Just a `mappend` Just b = Just (a `mappend` b)
  sconcat (NonEmpty h t) = foldlList mappend h t
  
  
instance Semigroup a => Monoid (Maybe a) where
  mempty = Nothing
  mconcat = foldrList mappend mempty

instance VSemigroup a => VSemigroup (Maybe a) where
  lawAssociative (Just x) (Just y) (Just z) = lawAssociative x y z
  lawAssociative _ _ _ = ()
  lawSconcat _ = ()

instance VMonoid a => VMonoid (Maybe a) where
  lawMconcat xs = mconcat xs `cast` ()
  lawEmpty Nothing = ()
  
  lawEmpty (Just x) = () -- lawEmpty x `cast` ()
