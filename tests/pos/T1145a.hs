{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
-- | Test that LH can load fine the specification for F,
-- then test in T1145b that LH can load fine the specification for F from
-- an imported module.
module T1145a where

import Data.Kind
import GHC.TypeNats

{-@ embed Natural as Int @-}

{-@ type BoundedInteger N = { i : Integer | N > 0 && i >= 0 && i < N } @-}
{-@ data Fin n = F Integer @-}
{-@ F :: forall (n :: Nat). BoundedInteger n -> Fin n @-}
type Fin :: Nat -> Type
data Fin n = F Integer
