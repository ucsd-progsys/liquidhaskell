{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators         #-}

-- | Tests for Nat-indexed vectors (issue #2702).
--
-- Exercises type-level Nat support in LiquidHaskell:
--   * Value-kinded type variables (Nat) used in refinements
--   * Type-level numeric literals handled by typeSort (not falling to FObj)
--   * Measures on GADTs with Nat parameters
--
module TypeLitNatVec where

import Data.Kind (Type)
import GHC.TypeNats (Nat, Natural, type (+))

{-@ embed Natural as Int @-}

-- ---------------------------------------------------------------------------
-- Vec: length-indexed vector using a Nat GADT index.
-- ---------------------------------------------------------------------------

type Zero = 0
type Succ n = n + 1
{-@ data Vec [vlen] n a where
      VNil  :: Vec Zero a
      VCons :: forall a n. a -> Vec n a -> Vec (Succ n) a @-}
type Vec :: Nat -> Type -> Type
data Vec n a where
  VNil  :: Vec 0 a
  VCons :: a -> Vec n a -> Vec (Succ n) a

-- ---------------------------------------------------------------------------
-- Measure: vlen counts the number of elements.
-- ---------------------------------------------------------------------------

{-@ measure vlen @-}
{-@ vlen :: forall n a. Vec n a -> Nat @-}
vlen :: Vec n a -> Int
vlen VNil         = 0
vlen (VCons _ xs) = 1 + vlen xs

-- ---------------------------------------------------------------------------
-- Safe index: precondition 0 <= i < n uses the type-level Nat parameter.
-- This tests that value-kinded type variables can appear in refinements.
-- Note: VNil branch uses 'undefined' without a 'false' precondition since
-- GADT coercion evidence (n~0) is not yet leveraged by LH.
-- ---------------------------------------------------------------------------

{-@ at :: forall (n :: Nat). v:Vec n a -> {i : Nat | i < n} -> a @-}
at :: Vec n a -> Int -> a
at (VCons x _)  0 = x
at (VCons _ xs) i = xs `at` (i - 1)
at VNil         _ = undefined

-- ---------------------------------------------------------------------------
-- Head: requires n >= 1, testing Nat in refinements.
-- ---------------------------------------------------------------------------

{-@ hd :: forall (n :: Nat). {v : Vec n a | 1 <= n} -> a @-}
hd :: Vec n a -> a
hd (VCons x _) = x
hd VNil        = undefined
