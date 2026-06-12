{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--prune-unsorted" @-}

-- | Tests for Nat type literals in LH specs (issue #2447).
--
-- When a data type is indexed by a concrete Nat literal, LH should
-- substitute the literal value for the type parameter in the constructor's
-- refinements at the case-split site.  This makes it possible to:
--
--   * Detect that @EmptyIfZero 0@ is uninhabited (precondition @0 /= 0@
--     is false), making an exhaustive pattern match on it safe.
--   * Establish that @Exact 3@ holds a value equal to @3@ after matching.
module NatLit where

import Data.Kind (Type)
import GHC.TypeNats (Nat, Natural)

{-@ embed Natural as Int @-}

-- ---------------------------------------------------------------------------
-- EmptyIfZero: constructor requires n /= 0, so EmptyIfZero 0 is uninhabited.
-- ---------------------------------------------------------------------------

{-@ data EmptyIfZero n = EmptyIfZero Int @-}
{-@ EmptyIfZero :: forall (n :: Nat). {v : Int | n /= 0} -> EmptyIfZero n @-}
type EmptyIfZero :: Nat -> Type
data EmptyIfZero n = EmptyIfZero Int

-- Construction at n=1: 1 /= 0 is satisfied for any Int field value.
mkOne :: EmptyIfZero 1
mkOne = EmptyIfZero 42

-- Construction at n=3: likewise safe.
mkThree :: EmptyIfZero 3
mkThree = EmptyIfZero 0

-- Pattern matching on EmptyIfZero 0 is safe: after unfolding the constructor
-- at 0 the environment contains {v:Int | 0 /= 0} = {v:Int | false}, which is
-- contradictory, so the branch is unreachable.
absurdZero :: EmptyIfZero 0 -> Int
absurdZero (EmptyIfZero _) = error "unreachable"

-- ---------------------------------------------------------------------------
-- Exact: constructor stores a value equal to n; matching reveals the equality.
-- ---------------------------------------------------------------------------

{-@ data Exact n = Exact Int @-}
{-@ Exact :: forall (n :: Nat). {v : Int | v == n} -> Exact n @-}
type Exact :: Nat -> Type
data Exact n = Exact Int

-- Construction at n=5: the field must equal 5.
mkExact5 :: Exact 5
mkExact5 = Exact 5

-- After pattern-matching, the result is constrained to equal the literal.
{-@ getExact3 :: Exact 3 -> {v : Int | v == 3} @-}
getExact3 :: Exact 3 -> Int
getExact3 (Exact v) = v

-- Polymorphic getter: the returned value equals the Nat type parameter.
{-@ getExact :: forall (n :: Nat). Exact n -> {v : Int | v == n} @-}
getExact :: Exact n -> Int
getExact (Exact v) = v
