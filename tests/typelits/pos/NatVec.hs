{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators         #-}

-- | Tests for Nat-indexed vectors (issue #2702).
--
-- @Vec n a@ is a GADT where the index @n@ counts elements exactly.  The
-- safe-index operation @at@ requires @0 <= i < vlen v@.  When the scrutinee
-- is @VNil@, the GADT constraint reveals @n = 0@, hence @vlen v = 0@, making
-- the precondition vacuously false and the branch unreachable.
--
-- The test exercises:
--   * GADT constructors with Nat literals (@Vec 0 a@) and arithmetic
--     (@Vec (n+1) a@) in return types
--   * A measure @vlen@ that counts structural elements
--   * Safe indexing that is verified by LH to be total
--
module NatVec where

import Data.Kind (Type)
import GHC.TypeNats (Nat, Natural, type (+), type (-))

{-@ embed Natural as Int @-}

-- ---------------------------------------------------------------------------
-- Vec: length-indexed vector using a Nat GADT index.
-- ---------------------------------------------------------------------------

-- TODO: make Zero and Succ unnecessary by using 0 and (n + 1) directly in the
-- GADT constructor return type.
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
{-@ vlen :: forall n a. Vec n a -> {v:Nat | n == v} @-}
vlen :: Vec n a -> Int
vlen VNil         = 0
vlen (VCons _ xs) = 1 + vlen xs

-- ---------------------------------------------------------------------------
-- Safe index: precondition 0 <= i < vlen v ensures no out-of-bounds access.
-- ---------------------------------------------------------------------------

{-@ at :: forall (n :: Nat). v:Vec n a -> {i : Nat | i < n} -> a @-}
at :: Vec n a -> Int -> a
at VNil         _ = error "unreachable: VNil has vlen 0 so precondition is false"
at (VCons x _)  0 = x
at (VCons _ xs) i = xs `at` (i - 1)

-- ---------------------------------------------------------------------------
-- Simple constructors for use in properties below.
-- ---------------------------------------------------------------------------

-- A three-element vector.
vec3 :: Vec 3 Int
vec3 = VCons 10 (VCons 20 (VCons 30 VNil))

-- Accessing the first element is safe: 0 < vlen vec3 = 3.
{-@ firstElem :: {v : Int | v == 10} @-}
firstElem :: Int
firstElem = vec3 `at` 0

-- Accessing the last element is safe: 2 < vlen vec3 = 3.
{-@ lastElem :: {v : Int | v == 30} @-}
lastElem :: Int
lastElem = vec3 `at` 2

-- ---------------------------------------------------------------------------
-- Head with a refined type.
-- ---------------------------------------------------------------------------

-- hd is only safe for non-empty vectors (vlen >= 1).
{-@ hd :: forall n a. {v : Vec n a | 1 <= n} -> a @-}
hd :: Vec n a -> a
hd (VCons x _) = x
hd VNil        = error "unreachable"

