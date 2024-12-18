{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Num.Integer_LHAssumptions() where

import GHC.Prim
import GHC.Num.Integer
import GHC.Types_LHAssumptions()

{-@
assume GHC.Num.Integer.IS :: x:Int# -> {v: Integer | v = (x :: int) }

embed Integer as int
@-}
