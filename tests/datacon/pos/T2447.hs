{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-- | Test for https://github.com/ucsd-progsys/liquidhaskell/issues/2447
-- Empty data types parameterised by type-level Nat literals should work as
-- expected: when the literal makes the constructor condition false the type is
-- uninhabited, so pattern-matching on it must be accepted.
--
-- Also tests that argType handles type-level Nat arithmetic (n+1, n*2, etc.)
-- so the corresponding symbols are substituted correctly.

{-# LANGUAGE TypeOperators #-}

module T2447 where

import GHC.Base    (Type)
import GHC.TypeNats (Nat, Natural, type (+))

{-@ embed Natural as Int @-}

-- ---------------------------------------------------------------------------
-- Test 1: simple type literal
-- ---------------------------------------------------------------------------

{-@ type FalseIfZero N = { i : Int | N /= 0 } @-}
{-@ data EmptyIfZero n = EmptyIfZero Int @-}
{-@ EmptyIfZero :: forall (n :: Nat). FalseIfZero n -> EmptyIfZero n @-}
type EmptyIfZero :: Nat -> Type
data EmptyIfZero n = EmptyIfZero Int

-- Construction at non-zero: accepted (the field value satisfies 1 /= 0)
someNonZeroT :: EmptyIfZero 1
someNonZeroT = EmptyIfZero 1

-- Pattern matching on EmptyIfZero 0 should be accepted because
-- the branch is unreachable (the type is uninhabited).
getSomeZeroT :: EmptyIfZero 0 -> Int
getSomeZeroT (EmptyIfZero _) = error "unreachable"

-- ---------------------------------------------------------------------------
-- Test 2: type-level arithmetic (n + 1)
-- The constructor refines the field to be equal to n+1, so matching on
-- `SumSucc 0` reveals the field equals 1.
-- ---------------------------------------------------------------------------

{-@ data SumSucc n = SumSucc Int @-}
{-@ SumSucc :: forall (n :: Nat). {v : Int | v == n + 1 } -> SumSucc n @-}
type SumSucc :: Nat -> Type
data SumSucc n = SumSucc Int

{-@ getSumSucc3 :: forall (n :: Nat). SumSucc n -> {v:Int | v == n + 1} @-}
getSumSucc3 :: SumSucc n -> Int
getSumSucc3 (SumSucc v) = v  -- v equals 4 in the environment
