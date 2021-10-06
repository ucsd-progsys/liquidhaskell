{-# LANGUAGE RankNTypes #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--aux-inline" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--noadt" @-}

module Data.List.Foldable where
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

{-@ lemmaAppEndo :: f:(a -> a) -> g:Endo a -> z:a -> {appEndo (mappend (Endo f) g) z = f (appEndo g z)} @-}
lemmaAppEndo :: (a -> a) -> Endo a -> a -> ()
lemmaAppEndo f (Endo g) z = ()

instance Foldable List where
  foldr f z Nil = z
  foldr f z (Cons x xs) = f x (foldr f z xs)
  foldMap f Nil = mempty
  foldMap f (Cons x xs) = f x `mappend` foldMap f xs

instance VFoldable List where
  lawFoldable1 f z Nil  = ()
  lawFoldable1 f z (Cons x xs) =
    lawFoldable1 f z xs `cast`
    lemmaAppEndo (f x) (foldMap (composeEndo f) xs) z  `cast`
    ()
