{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Functor.Const.Functor where
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
import Data.Functor.Const
import Data.Functor.Classes
import Liquid.ProofCombinators
import Data.Function




instance Functor (Const m) where
  fmap _ (Const v) = Const v
  _ <$ (Const v) = Const v

instance VFunctor (Const m) where
  lawFunctorId (Const v) = ()
  lawFunctorComposition _ _ _ = ()
