module GHC.Prim (module Exports) where

{-@ embed GHC.Prim.Int# as int @-}
{-@ class measure len :: forall f a. f a -> GHC.Prim.Int# @-}
import "ghc-prim" GHC.Prim as Exports
