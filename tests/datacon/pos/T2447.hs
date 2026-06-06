{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-- | Test for https://github.com/ucsd-progsys/liquidhaskell/issues/2447
-- Empty data types parameterised by type-level Nat literals should work as
-- expected: when the literal makes the constructor condition false the type is
-- uninhabited, so pattern-matching on it must be accepted.

module T2447 where

import GHC.Base    (Type)
import GHC.TypeNats (Nat, Natural)

{-@ embed Natural as Int @-}

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
