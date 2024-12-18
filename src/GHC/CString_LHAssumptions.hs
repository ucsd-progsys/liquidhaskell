{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.CString_LHAssumptions() where

import GHC.CString
import GHC.Prim
import GHC.Types_LHAssumptions()

_f = unpackCString#

{-@
assume GHC.CString.unpackCString#
  :: x:Addr#
  -> {v:[Char] | v ~~ x && len v == strLen x}
@-}
