{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Ptr_LHAssumptions where

import GHC.Ptr
import GHC.Types_LHAssumptions()

{-@
measure pbase     :: Ptr a -> Int
measure plen      :: Ptr a -> Int
measure isNullPtr :: Ptr a -> Bool

type PtrN a N = {v: PtrV a        | plen v == N }
type PtrV a   = {v: Ptr a | 0 <= plen v }

assume castPtr :: p:(PtrV a) -> (PtrN b (plen p))

assume plusPtr :: base:(PtrV a)
                -> off:{v:Int | v <= plen base }
                -> {v:(PtrV b) | pbase v = pbase base && plen v = plen base - off}

assume minusPtr :: q:(PtrV a)
                 -> p:{v:(PtrV b) | pbase v == pbase q && plen v >= plen q}
                 -> {v:Nat | v == plen p - plen q}

measure deref     :: Ptr a -> a
@-}
