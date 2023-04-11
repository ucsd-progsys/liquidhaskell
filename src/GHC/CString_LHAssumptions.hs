{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module GHC.CString_LHAssumptions() where

import GHC.CString
import GHC.Types_LHAssumptions()

_f = unpackCString#

{-@
measure strLen :: Addr# -> GHC.Types.Int

GHC.CString.unpackCString#
  :: x:GHC.Prim.Addr#
  -> {v:[Char] | v ~~ x && len v == strLen x}
@-}
