-- | This module defines a type alias whose name conflicts with the one defined
-- in 'Nat1'. It is imported by 'QualifiedTypeAlias' and 'ImportedTypeAlias'
-- to test the import/export behavior of conflicting names.
module Nat2 where

import Data.Int (Int32)
import NatFoo ()

{-@ type INat = {v:Int32 | v >= 0}@-}
