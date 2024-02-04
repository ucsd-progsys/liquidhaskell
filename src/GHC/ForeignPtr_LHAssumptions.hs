{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.ForeignPtr_LHAssumptions where

import GHC.ForeignPtr
import GHC.Ptr_LHAssumptions()

{-@
measure fplen :: GHC.Internal.ForeignPtr.ForeignPtr a -> GHC.Types.Int

type ForeignPtrV a   = {v: GHC.Internal.ForeignPtr.ForeignPtr a | 0 <= fplen v}
type ForeignPtrN a N = {v: GHC.Internal.ForeignPtr.ForeignPtr a | 0 <= fplen v && fplen v == N }

assume GHC.Internal.ForeignPtr.newForeignPtr_     :: p:(GHC.Internal.Ptr.Ptr a) -> (GHC.Types.IO (ForeignPtrN a (plen p)))
assume GHC.Internal.ForeignPtr.mallocPlainForeignPtrBytes :: n:{v:GHC.Types.Int  | v >= 0 } -> (GHC.Types.IO (ForeignPtrN a n))
@-}
