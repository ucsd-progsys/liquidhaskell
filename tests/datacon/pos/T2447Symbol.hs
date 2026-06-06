{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-- | Tests for Symbol-kinded type arguments in LH specs.
--
-- A type parameterised by a 'Symbol' kind carries a tag whose value is a
-- type-level string.  LH should accept specs that use Symbol literals in type
-- positions (written @("some string")@) and check refinement constraints
-- correctly.

module T2447Symbol where

import GHC.Base    (Type)
import GHC.TypeLits (Symbol)

-- ---------------------------------------------------------------------------
-- A container tagged by a Symbol, whose Int field must be non-negative.
-- ---------------------------------------------------------------------------

type Bucket :: Symbol -> Type
data Bucket s = Bucket String Int

{-@ data Bucket s = Bucket String Int @-}
{-@ Bucket :: forall (s :: Symbol). {n:String | s == n} -> {v:Int | v >= 0} -> Bucket s @-}

-- Construction at a concrete Symbol tag: field must satisfy v >= 0.
emptyFoo :: Bucket "foo"
emptyFoo = Bucket "foo" 0

-- Spec uses a Symbol literal in parens to fix the tag to "bar".
-- The return constraint v >= 0 follows from the constructor invariant.
{-@ getBucketSize :: Bucket "bar" -> {v:Int | v >= 0} @-}
getBucketSize :: Bucket "bar" -> Int
getBucketSize (Bucket "bar" n) = n

-- Polymorphic over any Symbol tag.
{-@ identBucket :: forall (s :: Symbol). Bucket s -> Bucket s @-}
identBucket :: Bucket s -> Bucket s
identBucket b = b
