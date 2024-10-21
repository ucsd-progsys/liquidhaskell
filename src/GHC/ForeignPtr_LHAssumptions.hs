{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.ForeignPtr_LHAssumptions where

import GHC.ForeignPtr
import GHC.Ptr
import GHC.Ptr_LHAssumptions()

{-@
measure fplen :: ForeignPtr a -> Int

type ForeignPtrV a   = {v: ForeignPtr a | 0 <= fplen v}
type ForeignPtrN a N = {v: ForeignPtr a | 0 <= fplen v && fplen v == N }

assume GHC.Internal.ForeignPtr.newForeignPtr_     :: p:(Ptr a) -> (IO (ForeignPtrN a (plen p)))
assume GHC.Internal.ForeignPtr.mallocPlainForeignPtrBytes :: n:{v:Int  | v >= 0 } -> (IO (ForeignPtrN a n))
@-}
