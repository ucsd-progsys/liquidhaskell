{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Ptr_LHAssumptions where

import GHC.Ptr
import GHC.Types_LHAssumptions()

{-@
measure pbase     :: GHC.Internal.Ptr.Ptr a -> GHC.Types.Int
measure plen      :: GHC.Internal.Ptr.Ptr a -> GHC.Types.Int
measure isNullPtr :: GHC.Internal.Ptr.Ptr a -> Bool 

type PtrN a N = {v: PtrV a        | plen v == N }
type PtrV a   = {v: GHC.Internal.Ptr.Ptr a | 0 <= plen v }

assume GHC.Internal.Ptr.castPtr :: p:(PtrV a) -> (PtrN b (plen p))

assume GHC.Internal.Ptr.plusPtr :: base:(PtrV a)
                -> off:{v:GHC.Types.Int | v <= plen base }
                -> {v:(PtrV b) | pbase v = pbase base && plen v = plen base - off}

assume GHC.Internal.Ptr.minusPtr :: q:(PtrV a)
                 -> p:{v:(PtrV b) | pbase v == pbase q && plen v >= plen q}
                 -> {v:Nat | v == plen p - plen q}

measure deref     :: GHC.Internal.Ptr.Ptr a -> a
@-}
