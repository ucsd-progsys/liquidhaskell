{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--prune-unsorted" @-}

-- | Tests for Haskell type synonyms and closed type families involving Nat,
-- used as type arguments in LH specs.
--
-- GHC expands transparent type synonyms (e.g. @Zero@, @Two@) before LH
-- processes them, so LH ultimately sees the underlying literal or arithmetic
-- expression.  Closed type families (e.g. @Plus2@) are reduced by GHC during
-- type-checking, so LH sees only the reduced literal.
--
-- The test exercises:
--   * Nat type synonyms for literals (@Zero = 0@, @Two = 2@)
--   * Nat type synonyms for arithmetic (@Succ n = n + 1@)
--   * Closed type families (@Plus2 n = n + 2@, reduced at compile time)
module NatTypeSyn where

import Data.Kind (Type)
import GHC.TypeNats (Nat, Natural, type (+))

{-@ embed Natural as Int @-}

-- ---------------------------------------------------------------------------
-- Type synonyms for Nat literals.
-- ---------------------------------------------------------------------------

type Zero = 0 :: Nat
type Two  = 2 :: Nat
type Ten  = 10 :: Nat

-- ---------------------------------------------------------------------------
-- Type synonym for arithmetic (Succ expands to n+1).
-- ---------------------------------------------------------------------------

type Succ n = n + 1

-- ---------------------------------------------------------------------------
-- Closed type family (GHC reduces Plus2 n = n+2 at the call site).
-- ---------------------------------------------------------------------------

type family Plus2 (n :: Nat) :: Nat where
  Plus2 n = n + 2

-- ---------------------------------------------------------------------------
-- Exact: stores a value equal to its Nat parameter.
-- ---------------------------------------------------------------------------

{-@ data Exact n = Exact Int @-}
{-@ Exact :: forall (n :: Nat). {v : Int | v == n} -> Exact n @-}
type Exact :: Nat -> Type
data Exact n = Exact Int

-- Using the Zero synonym: expands to Exact 0, field must equal 0.
mkExactZero :: Exact Zero
mkExactZero = Exact 0

-- Using the Two synonym: expands to Exact 2, field must equal 2.
mkExactTwo :: Exact Two
mkExactTwo = Exact 2

-- Using the Succ synonym: Succ 4 = 4+1 = 5, field must equal 5.
mkExactSucc4 :: Exact (Succ 4)
mkExactSucc4 = Exact 5

-- Using the Plus2 type family: Plus2 3 reduces to 5, field must equal 5.
mkExactPlus2_3 :: Exact (Plus2 3)
mkExactPlus2_3 = Exact 5

-- ---------------------------------------------------------------------------
-- Pattern-match with a type synonym: reveals the concrete value.
-- ---------------------------------------------------------------------------

{-@ getExactZero :: Exact Zero -> {v : Int | v == 0} @-}
getExactZero :: Exact Zero -> Int
getExactZero (Exact v) = v

{-@ getExactSucc5 :: Exact (Succ 5) -> {v : Int | v == 6} @-}
getExactSucc5 :: Exact (Succ 5) -> Int
getExactSucc5 (Exact v) = v
