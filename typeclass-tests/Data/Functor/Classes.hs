{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Functor.Classes where

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
                                                )

import Data.Function
class Functor f where
  {-@ fmap :: forall a b. (a -> b) -> f a -> f b @-}
  fmap :: (a -> b) -> f a -> f b
  (<$) :: a -> f b -> f a

class Functor m => VFunctor m where
    {-@ lawFunctorId :: forall a . x:m a -> {fmap id x == id x} @-}
    lawFunctorId :: m a -> ()

    {-@ lawFunctorComposition :: forall a b c . f:(b -> c) -> g:(a -> b) -> x:m a -> { fmap (compose f g) x == compose (fmap f) (fmap g) x } @-}
    lawFunctorComposition :: forall a b c. (b -> c) -> (a -> b) -> m a -> ()

class Functor f => Applicative f where
  {-@ pure :: forall a. a -> f a @-}
  pure :: a -> f a
  {-@ ap :: forall a b. f (a -> b) -> f a -> f b @-}
  ap :: f (a -> b) -> f a -> f b
  {-@ liftA2 :: forall a b c. (a -> b -> c) -> f a -> f b -> f c @-}
  liftA2 :: forall a b c. (a -> b -> c) -> f a -> f b -> f c
  (*>) :: f a -> f b -> f b
  (<*) :: f a -> f b -> f a


class (VFunctor f, Applicative f) => VApplicative f where
  {-@ lawApplicativeId :: forall a . v:f a -> {ap (pure id) v = v} @-}
  lawApplicativeId :: f a -> ()

  {-@ lawApplicativeComposition :: forall a b c . u:f (b -> c) -> v:f (a -> b) -> w:f a -> {ap (ap (ap (pure compose) u) v) w = ap u (ap v w)} @-}
  lawApplicativeComposition :: forall a b c. f (b -> c) -> f (a -> b) -> f a -> ()

  {-@ lawApplicativeHomomorphism :: forall a b . g:(a -> b) -> x:a -> {px:f a | px = pure x} -> {ap (pure g) px = pure (g x)} @-}
  lawApplicativeHomomorphism :: forall a b. (a -> b) -> a -> f a -> ()

  {-@ lawApplicativeInterchange :: forall a b . u:f (a -> b) -> y:a -> {ap u (pure y) = ap (pure (flip apply y)) u} @-}
  lawApplicativeInterchange :: forall a b . f (a -> b) -> a -> ()


class Applicative m => Monad m where
  {-@ bind :: forall a b. m a -> (a -> m b) -> m b @-}
  bind :: forall a b. m a -> (a -> m b) -> m b
  return :: forall a. a -> m a
  mseq :: forall a b. m a -> m b -> m b

class (VApplicative m, Monad m) => VMonad m where
  {-@ lawMonad1 :: forall a b. x:a -> f:(a -> m b) -> {f x == bind (return x) f} @-}
  lawMonad1 :: forall a b. a -> (a -> m b) -> ()
  {-@ lawMonad2 :: forall a. m:m a -> {bind m return == m }@-}
  lawMonad2 :: forall a. m a -> ()
  {-@ lawMonad3 :: forall a b c. m:m a -> f:(a -> m b) -> g:(b -> m c) -> {h:(y:a -> {v0:m c | v0 = bind (f y) g}) | True} -> {bind (bind m f) g == bind m h} @-}
  lawMonad3 :: forall a b c. m a -> (a -> m b) -> (b -> m c) -> (a -> m c) -> ()
  -- iff is buggy
  {-@ lawMonadReturn :: forall a. x:a -> y:m a -> {((y == pure x) => (y == return x)) && ((y == return x) => (y == pure x)) } @-}
  lawMonadReturn :: forall a. a -> m a -> ()



-- {-@ reflect kcompose @-}
-- kcompose :: Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
-- kcompose f g x = bind (f x) g

-- {-@ kcomposeAssoc :: Monad m => f:(a -> m b) -> g:(b -> m c) -> h:(c -> m d) -> x:a -> {kcompose (kcompose f g) h x == kcompose f (kcompose g h) x} @-}
-- kcomposeAssoc :: VMonad m => (a -> m b) -> (b -> m c) -> (c -> m d) -> a -> ()
-- kcomposeAssoc f g h x = lawMonad3  (f x) g h (kcompose g h)
