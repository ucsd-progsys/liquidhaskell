{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--expect-any-error"  @-}
{-@ LIQUID "--prune-unsorted"    @-}

-- | Negative test: incorrect Nat arithmetic claim must be rejected.
--
-- @Counter n@ stores a value equal to @n@.  The function @getCounter@
-- pattern-matches on @Counter (n+1)@ and claims the result equals @n+2@.
-- After substituting @n+1@ for the constructor's type variable, the field
-- type is @{v:Int | v == n+1}@, which contradicts the postcondition
-- @{v:Int | v == n+2}@.  LH should report an unsafe constraint.
module NatArithUnsafe where

import Data.Kind (Type)
import GHC.TypeNats (Nat, Natural, type (+))

{-@ embed Natural as Int @-}

{-@ data Counter n = Counter Int @-}
{-@ Counter :: forall (n :: Nat). {v : Int | v == n} -> Counter n @-}
type Counter :: Nat -> Type
data Counter n = Counter Int

-- Wrong postcondition: claims v == n+2 but the field actually equals n+1.
{-@ getCounter :: forall (n :: Nat). Counter (n + 1) -> {v : Int | v == n + 2} @-}
getCounter :: Counter (n + 1) -> Int
getCounter (Counter v) = v
