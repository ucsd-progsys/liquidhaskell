-- | This module defines a type alias whose name conflicts with the one defined
-- in 'Nat2'. It is imported by 'QualifiedTypeAlias' and 'ImportedTypeAlias'
-- to test the import/export behavior of conflicting names.
module Nat1 where

import NatFoo ()

{-@ type INat = {v:Int | v >= 0} @-}
