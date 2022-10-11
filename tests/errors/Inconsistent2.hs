{-@ LIQUID "--expect-error-containing=Specified type does not refine Haskell type for `Inconsistent2.foo` (Checked)" @-}
module Inconsistent2 where

{-@ foo :: Nat @-}
foo :: Bool
foo = True
