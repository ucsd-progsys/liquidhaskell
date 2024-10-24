{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Foreign.C.String_LHAssumptions where

import Foreign.C.Types
import Foreign.Ptr_LHAssumptions()
import GHC.Ptr
import GHC.Types_LHAssumptions()

{-@
type CStringLen    = ((Ptr CChar), Nat)<{\p v -> (v <= (plen p))}>
type CStringLenN N = ((Ptr CChar), {v:Nat | v = N})<{\p v -> (v <= (plen p))}>

// measure cStringLen :: CStringLen -> Int
measure cStringLen :: ((Ptr CChar), Int) -> Int

// measure cStringLen :: ((Ptr CChar), Int) -> Int
// cStringLen (c, n) = n
@-}
