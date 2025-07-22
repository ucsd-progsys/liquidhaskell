-- | This module defines a type alias whose name conflicts with the one defined
-- in 'Nat2'. It exists solely to be imported by another module (e.g., 'AmbiguousTypeAlias').
module Nat1 where

{-@ type INat = {v:Int | v >= 0} @-}
