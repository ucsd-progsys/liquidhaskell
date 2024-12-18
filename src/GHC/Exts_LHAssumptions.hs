{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Exts_LHAssumptions where

import GHC.Base
import GHC.Prim
import GHC.Types_LHAssumptions()

{-@

assume GHC.Prim.+#  :: x:Int# -> y:Int# -> {v: Int# | v = x + y}
assume GHC.Prim.-#  :: x:Int# -> y:Int# -> {v: Int# | v = x - y}
assume GHC.Prim.==# :: x:Int# -> y:Int# -> {v:Int# | v = 1 <=> x = y}
assume GHC.Prim.>=# :: x:Int# -> y:Int# -> {v:Int# | v = 1 <=> x >= y}
assume GHC.Prim.<=# :: x:Int# -> y:Int# -> {v:Int# | v = 1 <=> x <= y}
assume GHC.Prim.<#  :: x:Int# -> y:Int# -> {v:Int# | v = 1 <=> x < y}
assume GHC.Prim.>#  :: x:Int# -> y:Int# -> {v:Int# | v = 1 <=> x > y}

@-}
