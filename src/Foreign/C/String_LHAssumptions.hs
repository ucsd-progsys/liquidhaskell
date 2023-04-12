{-# OPTIONS_GHC -Wno-unused-imports #-}
module Foreign.C.String_LHAssumptions where

import Foreign.C.Types
import Foreign.Ptr_LHAssumptions()
import GHC.Ptr
import GHC.Types_LHAssumptions()

{-@
type CStringLen    = ((GHC.Ptr.Ptr Foreign.C.Types.CChar), Nat)<{\p v -> (v <= (plen p))}>
type CStringLenN N = ((GHC.Ptr.Ptr Foreign.C.Types.CChar), {v:Nat | v = N})<{\p v -> (v <= (plen p))}>

// measure cStringLen :: Foreign.C.String.CStringLen -> GHC.Types.Int
measure cStringLen :: ((GHC.Ptr.Ptr Foreign.C.Types.CChar), GHC.Types.Int) -> GHC.Types.Int

// measure cStringLen :: ((GHC.Ptr.Ptr Foreign.C.Types.CChar), GHC.Types.Int) -> GHC.Types.Int 
// cStringLen (c, n) = n
@-}
