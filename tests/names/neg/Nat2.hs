-- | This module defines a type alias whose name conflicts with the one defined
-- in 'Nat1'. It exists solely to be imported by another module (e.g., 'AmbiguousTypeAlias').
module Nat2 where

import Data.Int (Int32)

{-@ type INat = {v:Int32 | v >= 0}@-}
