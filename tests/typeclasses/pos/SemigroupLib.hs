{-# LANGUAGE RankNTypes #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}
{-@ LIQUID "--aux-inline" @-}
{-@ LIQUID "--ple" @-}

module SemigroupLib where

import           Prelude                 hiding ( Semigroup(..)
                                                , Monoid(..)
                                                , foldr
                                                , head
                                                , flip
                                                , tail
                                                , Maybe (..)
                                                , Foldable (..)
                                                )
import Lib

class Semigroup a where
    {-@ mappend :: a -> a -> a @-}
    mappend :: a -> a -> a
    sconcat :: NonEmpty a -> a

class Semigroup a => VSemigroup a where
    {-@ lawAssociative :: v:a -> v':a -> v'':a -> {mappend (mappend v v') v'' == mappend v (mappend v' v'')} @-}
    lawAssociative :: a -> a -> a -> ()

    {-@ lawSconcat :: ys:NonEmpty a -> {foldlList mappend (head' ys) (tail' ys) == sconcat ys} @-}
    lawSconcat :: NonEmpty a -> ()

class Semigroup a => Monoid a where
    {-@ mempty :: a @-}
    mempty :: a

    mconcat :: List a -> a

class (VSemigroup a, Monoid a) => VMonoid a where
    {-@ lawEmpty :: x:a -> {mappend x mempty == x && mappend mempty x == x} @-}
    lawEmpty :: a -> () -- JP: Call this lawIdentity?

    {-@ lawMconcat :: xs:List a -> {mconcat xs == foldrList mappend mempty xs} @-}
    lawMconcat :: List a -> ()
