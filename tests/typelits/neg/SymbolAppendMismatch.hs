{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--prune-unsorted" @-}

-- | Wrong @AppendSymbol@ claim should be rejected (Symbol analog of
-- @NatArithUnsafe.hs@).
--
-- @ConcatTag m n@ stores a string whose value must equal
-- @AppendSymbol m n@.  Constructing it with a string that does NOT equal
-- the concatenation of the two Symbol arguments is a type error that LH
-- should detect once it can reason about @AppendSymbol@.
--
-- Currently (HEAD, no feature code) LH cannot parse the @AppendSymbol@
-- refinement, so it reports @SAFE (0 constraints)@ instead of an error.
-- Once the feature is implemented, the incorrect construction below must be
-- rejected.
module SymbolAppendMismatch where

import Data.Kind (Type)
import GHC.TypeLits (Symbol, AppendSymbol)

{-@ data ConcatTag m n = ConcatTag { catVal :: {v : String | v == AppendSymbol m n} } @-}
type ConcatTag :: Symbol -> Symbol -> Type
data ConcatTag (m :: Symbol) (n :: Symbol) = ConcatTag { catVal :: String }

-- ERROR: "foobaz" ≠ AppendSymbol "foo" "bar" = "foobar".
{-@ mkBadFooBar :: ConcatTag "foo" "bar" @-}
mkBadFooBar :: ConcatTag "foo" "bar"
mkBadFooBar = ConcatTag "foobaz"
