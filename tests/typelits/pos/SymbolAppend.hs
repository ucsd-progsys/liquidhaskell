{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--prune-unsorted" @-}

-- | Tests for @AppendSymbol@ in LH specs (Symbol analog of @NatArith.hs@).
--
-- @AppendSymbol m n@ concatenates two type-level @Symbol@ values, giving
-- back a @Symbol@.  It is the direct analog of @(+)@ for @Nat@.
--
-- For LH to reason about @AppendSymbol@ it must:
--   1. Recognise @AppendSymbol@ as a known type-level Symbol operation and
--      map it to string-concatenation in Fixpoint (analogous to how
--      @natTyConBop@ maps @(+)@ to @EBin Plus@ for @Nat@).
--   2. Accept @RExprArg (AppendSymbol m n)@ in @checkAppTys@ / @tyCompat@
--      (commit 43496cf).
--   3. Distinguish @AppendSymbol@'s sort (@String@) from @Nat@-sorted
--      expressions (commit 77c0776).
--
-- Concrete cases with two known Symbol literals are normalised by GHC
-- (@AppendSymbol "foo" "bar"@ → @"foobar"@) before LH processes them, so
-- they exercise the literal path.  The polymorphic cases (@m@, @n@ are
-- direct type-variable arguments to @ConcatTag@) exercise the expression
-- path in the output-refinement position.
--
-- Note: @AppendSymbol@ is a non-injective type family, so functions that
-- take @ConcatTag (AppendSymbol m n) p@ as an argument (with free @m@, @n@)
-- have ambiguous type variables under GHC's standard rules.  Such tests are
-- omitted here; they would require @AllowAmbiguousTypes@.
module SymbolAppend where

import Data.Kind (Type)
import GHC.TypeLits (Symbol, AppendSymbol)

-- ---------------------------------------------------------------------------
-- ConcatTag m n: stores a string whose value equals AppendSymbol m n.
-- ---------------------------------------------------------------------------

{-@ data ConcatTag m n = ConcatTag { catVal :: {v : String | v == AppendSymbol m n} } @-}
type ConcatTag :: Symbol -> Symbol -> Type
data ConcatTag (m :: Symbol) (n :: Symbol) = ConcatTag { catVal :: String }

-- Concrete: AppendSymbol "foo" "bar" = "foobar".
mkFooBar :: ConcatTag "foo" "bar"
mkFooBar = ConcatTag "foobar"

-- Concrete: AppendSymbol "" "hello" = "hello" (empty-prefix identity).
mkEmptyHello :: ConcatTag "" "hello"
mkEmptyHello = ConcatTag "hello"

-- Concrete: AppendSymbol "hello" "" = "hello" (empty-suffix identity).
mkHelloEmpty :: ConcatTag "hello" ""
mkHelloEmpty = ConcatTag "hello"

-- Concrete: AppendSymbol "liquid" "haskell" = "liquidhaskell".
mkLiquidHaskell :: ConcatTag "liquid" "haskell"
mkLiquidHaskell = ConcatTag "liquidhaskell"

-- ---------------------------------------------------------------------------
-- Retrieving the value at a concrete type.
-- ---------------------------------------------------------------------------

{-@ getFooBar :: ConcatTag "foo" "bar" -> {v : String | v == "foobar"} @-}
getFooBar :: ConcatTag "foo" "bar" -> String
getFooBar (ConcatTag s) = s

-- ---------------------------------------------------------------------------
-- Polymorphic retrieval: for any m n, catVal equals AppendSymbol m n.
-- ---------------------------------------------------------------------------

{-@ getCat :: forall (m :: Symbol) (n :: Symbol).
               ConcatTag m n -> {v : String | v == AppendSymbol m n} @-}
getCat :: ConcatTag m n -> String
getCat (ConcatTag s) = s

-- ---------------------------------------------------------------------------
-- Concrete nested AppendSymbol: GHC reduces both arguments to literals,
-- so AppendSymbol "a" "b" normalises to "ab" before LH sees the type.
-- The ConcatTag data spec then checks "abc" == AppendSymbol "ab" "c".
-- ---------------------------------------------------------------------------

mkABC :: ConcatTag (AppendSymbol "a" "b") "c"
mkABC = ConcatTag "abc"

-- ---------------------------------------------------------------------------
-- AppendSymbol with the same symbol twice: AppendSymbol s s = s ++ s.
-- ---------------------------------------------------------------------------

{-@ getDoubled :: forall (s :: Symbol).
                  ConcatTag s s -> {v : String | v == AppendSymbol s s} @-}
getDoubled :: ConcatTag s s -> String
getDoubled (ConcatTag s) = s
