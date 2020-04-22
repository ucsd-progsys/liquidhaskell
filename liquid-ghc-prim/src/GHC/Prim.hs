module GHC.Prim (module Exports) where

{-@ embed GHC.Prim.Int#     as int @-}
{-@ embed GHC.Prim.Addr#    as Str @-}
{-@ embed GHC.Prim.Char#    as Char @-}
{-@ embed GHC.Prim.Double#  as real @-}
{-@ embed GHC.Prim.Float#   as real @-}
{-@ embed GHC.Prim.Word#    as int  @-}
{-@ GHC.Prim.+#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v: GHC.Prim.Int# | v = x + y} @-}
{-@ GHC.Prim.-#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v: GHC.Prim.Int# | v = x - y} @-}
{-@ GHC.Prim.==# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x = y} @-}
{-@ GHC.Prim.>=# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x >= y} @-}
{-@ GHC.Prim.<=# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x <= y} @-}
{-@ GHC.Prim.<#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x < y}  @-}
{-@ GHC.Prim.>#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x > y}  @-}

import "ghc-prim" GHC.Prim as Exports
