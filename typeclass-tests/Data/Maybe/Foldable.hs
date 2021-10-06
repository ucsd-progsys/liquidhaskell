{-# LANGUAGE RankNTypes #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--aux-inline" @-}
{-@ LIQUID "--ple" @-}


module Data.Maybe.Foldable where
import           Prelude                 hiding ( Semigroup(..)
                                                , Monoid(..)
                                                , foldr
                                                , head
                                                , flip
                                                , tail
                                                , Maybe (..)
                                                , Foldable (..)
                                                , id
                                                )
import Data.Semigroup.Classes
import Liquid.ProofCombinators
import Data.Endo
import Data.Functor.Identity
import Data.Dual
import Data.Function
import Data.List
import Data.List.NonEmpty
import Data.Maybe
import Data.Functor.Const

class Foldable t where
  {-@ foldMap :: forall a m. Monoid m => (a -> m) -> t a -> m @-}
  foldMap :: forall a m. Monoid m => (a -> m) -> t a -> m
  foldr :: (a -> b -> b) -> b -> t a -> b

class Foldable t => VFoldable t where
  {-@ lawFoldable1 :: forall a b. f:(a -> b -> b) -> z:b -> t:t a -> {foldr f z t == appEndo (foldMap (composeEndo f) t ) z} @-}
  lawFoldable1 :: forall a b . (a -> b -> b) -> b -> t a -> ()


{-@ reflect composeEndo @-}
composeEndo :: (b -> a -> a) -> b -> Endo a
composeEndo f x = Endo (f x)

{-@ reflect dualEndoFlip @-}
dualEndoFlip :: (a -> b -> a) -> b -> Dual (Endo a)
dualEndoFlip f x  = Dual (Endo (flip f x))


instance Semigroup (Endo a) where
  mappend (Endo f) (Endo g) = Endo (compose f g)
  sconcat (NonEmpty h t) = foldlList mappend h t

instance Monoid (Endo a) where
  mempty = Endo id
  mconcat = foldrList mappend mempty


instance Foldable Maybe where
  foldMap f Nothing = mempty
  foldMap f (Just x) = f x
  foldr f m Nothing = m
  foldr f m (Just x) = f x m

instance VFoldable Maybe where
  lawFoldable1 _ _ Nothing = ()
  lawFoldable1 _ _ _ = ()
