{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Num.Integer_LHAssumptions() where

import GHC.Prim
import GHC.Num
import GHC.Types_LHAssumptions()

{-@
assume IS :: x:Int# -> {v: Integer | v = (x :: int) }

define IS x = (x)

embed Integer as int
@-}
