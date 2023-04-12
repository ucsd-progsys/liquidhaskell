{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.ForeignPtr_LHAssumptions where

import GHC.ForeignPtr
import GHC.Ptr_LHAssumptions()

{-@
measure fplen :: GHC.ForeignPtr.ForeignPtr a -> GHC.Types.Int

type ForeignPtrV a   = {v: GHC.ForeignPtr.ForeignPtr a | 0 <= fplen v}
type ForeignPtrN a N = {v: GHC.ForeignPtr.ForeignPtr a | 0 <= fplen v && fplen v == N }

GHC.ForeignPtr.newForeignPtr_     :: p:(GHC.Ptr.Ptr a) -> (GHC.Types.IO (ForeignPtrN a (plen p)))
GHC.ForeignPtr.mallocPlainForeignPtrBytes :: n:{v:GHC.Types.Int  | v >= 0 } -> (GHC.Types.IO (ForeignPtrN a n))
@-}
