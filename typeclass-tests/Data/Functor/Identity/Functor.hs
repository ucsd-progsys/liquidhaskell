{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--aux-inline" @-}

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
import Data.Functor.Classes

instance Functor Identity where
  fmap f (Identity i) = Identity (f i)
  x <$ (Identity _) = Identity x

instance VFunctor Identity where
    lawFunctorId _ = ()
    lawFunctorComposition f g (Identity x) = ()


instance Applicative Identity where
  pure = Identity
  ap (Identity f) (Identity a) = Identity (f a)
  liftA2 f (Identity a) (Identity b) = Identity (f a b)
  a1 *> a2 = ap (id <$ a1) a2
  a1 <* a2 = liftA2 const a1 a2

instance VApplicative Identity where
  lawApplicativeId _ = ()
  lawApplicativeComposition (Identity f) (Identity g) (Identity x) = ()
  lawApplicativeHomomorphism f x (Identity y) = ()
  lawApplicativeInterchange (Identity f) _ = ()


instance Monad Identity where
  bind (Identity x) f = f x
  return = Identity
  mseq  _ x = x

instance VMonad Identity where
  lawMonad1 x f = ()
  lawMonad2 (Identity x) = ()
  lawMonad3 (Identity x) f g h = h x `cast` ()
  lawMonadReturn _ _ = ()
