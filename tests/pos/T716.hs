
-- | See https://github.com/ucsd-progsys/liquidhaskell/issues/716
--   due to the wierd case-of thwarting ANF, you need the qualifier from the
--   output type of `narrow16Word` (apparently we don't scrape assumes?) 
--   ELIMINATE does not cut it, as the relevant kvar happens to be non-linear...

{-@ LIQUID "--scrape-used-imports" @-}

module Blank where

import GHC.Exts
import GHC.Prim
import GHC.Word

-- denotes the offset at which bits are no longer guaranteed to be defined

{-@ measure undefinedOffset :: Word# -> Int @-}

{-@ assume byteSwap16# :: Word# -> {v:Word# | undefinedOffset v = 16} @-}

-- We need either the below qualifier, or the one from the refinement of
-- `Word`.Why are NEITHER generated automatically?

{-@ assume narrow16Word# :: Word# -> {v:Word# | undefinedOffset v = 64} @-}

{-@ data Word = W# (w :: {v:Word# | undefinedOffset v >= 64}) @-}

grabWord16_SAFE (Ptr ip#) = let x = byteSwap16# (indexWord16OffAddr# ip# 0#) in W# (narrow16Word# x)

grabWord16_UNSAFE (Ptr ip#) = W# (narrow16Word# (byteSwap16# (indexWord16OffAddr# ip# 0#)))

-- mkWord :: {v:Word# | undefinedOffset v >= 64} -> Word
-- mkWord = W#

