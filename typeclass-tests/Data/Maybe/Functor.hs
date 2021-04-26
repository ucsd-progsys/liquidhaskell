{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--aux-inline" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Maybe.Functor where
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
import Liquid.ProofCombinators
import Data.Function
import Data.Maybe
import Data.Functor.Classes

instance Functor Maybe where
  fmap _ Nothing = Nothing
  fmap f (Just x) = Just (f x)
  _ <$ Nothing = Nothing
  x <$ (Just _) = Just x

instance VFunctor Maybe where
    lawFunctorId Nothing = ()
    lawFunctorId (Just _) = ()
    lawFunctorComposition f g Nothing = ()
    lawFunctorComposition f g (Just x) = ()

instance Applicative Maybe where
  pure = Just
  ap Nothing _ = Nothing
  ap _ Nothing = Nothing
  ap (Just f) (Just x) = Just (f x)
  liftA2 f (Just a) (Just b) = Just (f a b)
  liftA2 f _       _       = Nothing
  a1 *> a2 = ap (id <$ a1) a2
  a1 <* a2 = liftA2 const a1 a2

instance VApplicative Maybe where
  lawApplicativeId Nothing = ()
  lawApplicativeId (Just x) = ap (pure id) (Just x) `cast` ()
  lawApplicativeComposition (Just f) (Just g) (Just x) = ()
  lawApplicativeComposition _ _ _ = ()
  lawApplicativeHomomorphism f x (Just y) = ()
  lawApplicativeHomomorphism f x Nothing = ()
  lawApplicativeInterchange Nothing _ = ()
  lawApplicativeInterchange (Just f) _ = ()


instance Monad Maybe where
  bind Nothing _ = Nothing
  bind (Just x) f = f x
  return = Just
  mseq _ (Just x) = Just x
  mseq _ Nothing = Nothing

instance VMonad Maybe where
  lawMonad1 x f = ()
  lawMonad2 Nothing = ()
  lawMonad2 (Just x) = ()
  lawMonad3 Nothing f g h = ()
  lawMonad3 (Just x) f g h = h x `cast` ()
  lawMonadReturn _ _ = ()
