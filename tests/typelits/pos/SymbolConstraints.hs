{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--prune-unsorted" @-}

-- | Tests for Symbol type variables used in refinement constraints.
--
-- When a type is parameterised by @s :: Symbol@, the type variable @s@ has
-- sort @[Char]@ in Fixpoint (because LH encodes @Symbol@ values as
-- @String = [Char]@).  This allows the refinement @v == s@ to express
-- that a stored string is exactly the Symbol argument.
--
-- The test exercises:
--   * A @NamedBucket s@ whose field must equal the Symbol parameter @s@.
--   * Construction at concrete Symbol literals.
--   * A function that returns the stored string at its expected type.
--   * A type alias @BucketOf S@ that abbreviates @NamedBucket S@.
--   * A predicate alias @HasName S V@ relating a string to a Symbol.
module SymbolConstraints where

import Data.Kind (Type)
import GHC.TypeLits (Symbol)

-- ---------------------------------------------------------------------------
-- NamedBucket: the stored name field must equal the Symbol parameter.
-- ---------------------------------------------------------------------------

{-@ data NamedBucket s = NamedBucket { nbName :: {v : String | v == s} } @-}
data NamedBucket (s :: Symbol) = NamedBucket { nbName :: String }

-- Construction: the literal "alice" satisfies v == "alice".
mkAlice :: NamedBucket "alice"
mkAlice = NamedBucket "alice"

-- Construction: the literal "bob" satisfies v == "bob".
mkBob :: NamedBucket "bob"
mkBob = NamedBucket "bob"

-- Retrieving the name recovers the Symbol value.
{-@ getAliceName :: NamedBucket "alice" -> {v : String | v == "alice"} @-}
getAliceName :: NamedBucket "alice" -> String
getAliceName (NamedBucket n) = n

-- Polymorphic: for any Symbol s, the stored name equals s.
{-@ getBucketName :: forall (s :: Symbol). NamedBucket s -> {v : String | v == s} @-}
getBucketName :: NamedBucket s -> String
getBucketName (NamedBucket n) = n

-- ---------------------------------------------------------------------------
-- Type alias: BucketOf S — abbreviates NamedBucket with a Symbol argument.
-- ---------------------------------------------------------------------------

{-@ type BucketOf S = NamedBucket S @-}

{-@ mkAdmin :: BucketOf "admin" @-}
mkAdmin :: NamedBucket "admin"
mkAdmin = NamedBucket "admin"

-- ---------------------------------------------------------------------------
-- Predicate alias: HasName S V — V (a String) equals the Symbol S.
-- ---------------------------------------------------------------------------

{-@ predicate HasName S V = V == S @-}

{-@ checkName :: forall (s :: Symbol). NamedBucket s -> {v : String | HasName s v} @-}
checkName :: NamedBucket s -> String
checkName (NamedBucket n) = n
