{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--aux-inline" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Either.Functor where
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
import Data.Either
import Data.Functor.Classes

instance Functor (Either l) where
  fmap f (Right x) = Right (f x)
  fmap f (Left x) = Left x
  x <$ (Right _) = Right x
  _ <$ (Left x)  = Left x

instance VFunctor (Either l) where
  lawFunctorId (Left _) = ()
  lawFunctorId _ = ()
  lawFunctorComposition _ _ (Left _) = ()
  lawFunctorComposition _ _ (Right _) = ()

instance Applicative (Either l) where
  pure = Right 
  ap (Right f) (Right x) = Right (f x)
  ap (Right f) (Left x)  = Left x
  ap (Left x) _ = Left x

  liftA2 f x y = pure f `ap` x `ap` y
  a1 *> a2 = ap (id <$ a1) a2
  a1 <* a2 = liftA2 const a1 a2

instance VApplicative (Either l) where
  lawApplicativeId (Left _) = ()
  lawApplicativeId _ = ()
  lawApplicativeComposition (Right _) (Right _) (Right _)  = ()
  lawApplicativeComposition _ _ _  = ()
  lawApplicativeHomomorphism f x (Left _) = ()
  lawApplicativeHomomorphism f x _ = ()
  lawApplicativeInterchange (Left _) _ = ()
  lawApplicativeInterchange (Right _) _ = ()

instance Monad (Either l) where
  return = Right
  bind (Right x) f = f x
  bind (Left x) f = Left x
  mseq (Right _) (Right x) = Right x
  mseq (Left x) _ = Left x
  mseq (Right _) (Left x) = Left x

instance VMonad (Either l) where
  lawMonad1 x f = ()
  lawMonad2 (Left _) = ()
  lawMonad2 _ = ()
  lawMonad3 (Right x) f g h = h x `cast` ()
  lawMonad3 _ _ _ _ = ()
  lawMonadReturn _ _ = ()
