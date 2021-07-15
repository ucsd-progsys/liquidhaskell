{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Maybe where
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
-- import Data.Functor.Classes

{-@ data Maybe a = Nothing | Just a @-}
data Maybe a = Nothing | Just a
{-@ data First a = First {getFirst :: Maybe a} @-}
data First a = First {getFirst :: Maybe a}
{-@ data Last a = Last {getLast :: Maybe a} @-}
data Last a = Last {getLast :: Maybe a}
