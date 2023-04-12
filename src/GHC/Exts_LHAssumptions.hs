{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Exts_LHAssumptions where

import GHC.Base
import GHC.Types_LHAssumptions()

{-@

GHC.Prim.+#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v: GHC.Prim.Int# | v = x + y}
GHC.Prim.-#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v: GHC.Prim.Int# | v = x - y}
GHC.Prim.==# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x = y}
GHC.Prim.>=# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x >= y}
GHC.Prim.<=# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x <= y}
GHC.Prim.<#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x < y}
GHC.Prim.>#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x > y}

@-}
