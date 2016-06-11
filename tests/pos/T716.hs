
-- | See https://github.com/ucsd-progsys/liquidhaskell/issues/716
-- due to the wierd case-of thwarting ANF, you need the qualifier from the
-- output type of `narrow16Word` (apparently we don't scrape assumes?) 
-- OR you need `eliminate` to do its business.

module Blank where

import GHC.Exts
import GHC.Prim
import GHC.Word

-- denotes the offset at which bits are no longer guaranteed to be defined

{-@ measure undefinedOffset :: Word# -> Int @-}

{-@ assume byteSwap16# :: Word# -> {v:Word# | undefinedOffset v = 16} @-}

{-@ assume narrow16Word# :: Word# -> {v:Word# | undefinedOffset v = 64} @-}


{-@ data Word = W# (w :: {v:Word# | undefinedOffset v >= 64}) @-}

grabWord16_SAFE (Ptr ip#) = let x = byteSwap16# (indexWord16OffAddr# ip# 0#) in W# (narrow16Word# x)

grabWord16_UNSAFE (Ptr ip#) = W# (narrow16Word# (byteSwap16# (indexWord16OffAddr# ip# 0#)))


-- works if you replace calls to narrow16Word# with bob
-- but why does `eliminate` not take care of it?
{- bob :: Word# -> {v:Word# | undefinedOffset v = 64} @-}
bob :: Word# -> Word#
bob = undefined
