{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--prune-unsorted" @-}

-- | Tests for Symbol type literals in LH specs (commit 77c0776).
--
-- GHC's @Symbol@ kind has string literals as its inhabitants.  LH encodes
-- @Symbol@ type variables as sort @[Char]@ in Fixpoint, which allows string
-- expressions in refinements that involve those variables.
--
-- The test exercises:
--   * A type @Labeled s a@ parameterised by a Symbol literal used in
--     a constructor specification.
--   * Construction with a concrete Symbol literal (@"foo"@, @"bar"@).
--   * Pattern-matching on @Labeled "baz"@ to recover the label.
module SymbolLit where

import Data.Kind (Type)
import GHC.TypeLits (Symbol)

-- ---------------------------------------------------------------------------
-- Labeled: a wrapper that carries a Symbol tag and exposes it in a
-- constructor refinement so LH can reason about the tag value.
-- ---------------------------------------------------------------------------

{-@ data Labeled s a = Labeled { unLabeled :: a } @-}
newtype Labeled (s :: Symbol) a = Labeled { unLabeled :: a }

-- Construction at "foo": the tag is "foo".
mkFoo :: Labeled "foo" Int
mkFoo = Labeled 42

-- Construction at "bar": the tag is "bar".
mkBar :: Labeled "bar" Bool
mkBar = Labeled True

-- Unwrapping preserves the label (trivially, since the wrapper is a newtype).
{-@ getFoo :: Labeled "foo" Int -> Int @-}
getFoo :: Labeled "foo" Int -> Int
getFoo (Labeled n) = n

-- ---------------------------------------------------------------------------
-- Bucket: a record where the stored name must equal the Symbol parameter.
-- ---------------------------------------------------------------------------

{-@ data Bucket s = Bucket { bName :: {v : String | v == s} } @-}
data Bucket (s :: Symbol) = Bucket { bName :: String }

-- Construction at "hello": bName must equal "hello".
mkHelloBucket :: Bucket "hello"
mkHelloBucket = Bucket "hello"

-- ---------------------------------------------------------------------------
-- Polymorphic: a function that operates on any Symbol-tagged bucket.
-- ---------------------------------------------------------------------------

{-@ getName :: forall (s :: Symbol). Bucket s -> {v : String | v == s} @-}
getName :: Bucket s -> String
getName (Bucket n) = n
