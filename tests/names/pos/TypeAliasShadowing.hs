-- | This test shows that type aliases from dependencies (in this case, @Nat@
-- from 'Prelude') can be shadowed by a local definition refining 'Integer'
-- instead of 'Int'.
-- The ambiguous ocurrence in 'foo' spec is resolved to the local definition
-- by default. Also, this definition is the one stored in the resulting
-- specification (the 'LiftedSpec' passed to clients).
-- This is shown in @tests/names/pos/ImportedTypeAliases@
module TypeAliasShadowing () where

-- We leave the imported @NatFoo@ alias unused to show that no ocurrence is needed
-- for it to be stored in the resulting spec.
import NatFoo ()

{-@ type Nat = {v:Integer | v >= 0} @-}

{-@ foo :: Nat @-}
foo :: Integer
foo = 0

{-@ bar :: TypeAliasShadowing.Nat @-}
bar :: Integer
bar = 1

{-@ baz :: Prelude.Nat @-}
baz :: Int
baz = 2
