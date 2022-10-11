{-# LANGUAGE RankNTypes #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}
module Lemma where

import Prelude hiding (Semigroup(..), mappend)

import SemigroupLib
-- YL: why is it necessary to include Lib?
import Lib

{-@ assoc4 :: VSemigroup a => x:a -> y:a -> z:a -> h:a -> {mappend x (mappend y (mappend z h)) == mappend (mappend  (mappend x y) z) h} @-}
assoc4 :: VSemigroup a => a -> a -> a -> a -> ()
assoc4 x y z h =
  () `const`
  mappend x (mappend y (mappend z h)) `const`
  lawAssociative y z h `const`
  mappend x (mappend (mappend y z) h) `const`
  lawAssociative x (mappend y z) h `const`
  mappend (mappend x (mappend y z)) h `const`
  lawAssociative x y z `const`
  mappend (mappend (mappend x y) z) h
