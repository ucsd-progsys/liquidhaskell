-- | This module defines a type alias as a refinement of another type alias.
module NatFoo () where

{-@ type NatFoo = {v:Nat | v >= 1}@-}
