module Data.ByteString.Lazy.Aux where

import Data.ByteString.Internal
import Data.Word

--LIQUID from Fusion
{-@ qualif PlusOnePos(v: Int): 0 <= (v + 1)                @-}
{-@ qualif LePlusOne(v: Int, x: Int): v <= (x + 1)         @-}
{-@ qualif LeDiff(v: a, x: a, y:a): v <= (x - y)           @-}
{-@ qualif PlenEq(v: GHC.Ptr.Ptr a, x: Int): x <= (plen v) @-}
{-@ qualif BlenEq(v: Int, x:Data.ByteString.Internal.ByteString): v = (bLength x)   @-}
{-@ qualif PSnd(v: a, x:b): v = (psnd x)                   @-}

--LIQUID from Internal
--LIQUID hack until we have proper name-resolution
{-@ type ByteString = {v:Data.ByteString.Internal.ByteString | true} @-}

{-@ qualif ByteStringN(v:Data.ByteString.Internal.ByteString, n:Int): (bLength v) = n @-}
{-@ qualif ByteStringNE(v:Data.ByteString.Internal.ByteString): (bLength v) > 0 @-}
{-@ qualif ByteStringSZ(v:Data.ByteString.Internal.ByteString,
                        b:Data.ByteString.Internal.ByteString):
        (bLength v) = (bLength b)
  @-}

{-@ qualif BLenAcc(v:int,
                   b1:Data.ByteString.Internal.ByteString,
                   b2:Data.ByteString.Internal.ByteString):
       v = (bLength b1) + (bLength b2)
  @-}
{-@ qualif BLenAcc(v:int,
                   b:Data.ByteString.Internal.ByteString,
                   n:int):
       v = (bLength b) + n
  @-}


{-@ qualif EqFPLen(v: a, x: GHC.ForeignPtr.ForeignPtr b): v = (fplen x) @-}
{-@ qualif EqPLen(v: a, x: GHC.Ptr.Ptr b): v = (plen x) @-}
{-@ qualif EqPLen(v: GHC.ForeignPtr.ForeignPtr a, x: GHC.Ptr.Ptr a): (fplen v) = (plen x) @-}
{-@ qualif EqPLen(v: GHC.Ptr.Ptr a, x: GHC.ForeignPtr.ForeignPtr a): (plen v) = (fplen x) @-}
{-@ qualif PValid(v: Int, p: GHC.Ptr.Ptr a): v <= (plen p) @-}
{-@ qualif PValid(v: Int, p: GHC.Ptr.Ptr a): v < (plen p) @-}
{-@ qualif PLLen(v:a, p:b) : (len v) <= (plen p) @-}
{-@ qualif FPLenPos(v: GHC.ForeignPtr.ForeignPtr a): 0 <= (fplen v) @-}
{-@ qualif PLenPos(v: GHC.Ptr.Ptr a): 0 <= (plen v) @-}

-- for ByteString.concat
{-@ qualif BLens(v:List Data.ByteString.Internal.ByteString)            : 0 <= (bLengths v)         @-}
{-@ qualif BLenLE(v:Ptr a, bs:List Data.ByteString.Internal.ByteString) : (bLengths bs) <= (plen v) @-}
{-@ qualif BLenLE(v:Data.ByteString.Internal.ByteString, n:int): (bLength v) <= n @-}

-- for ByteString.splitWith
{-@ qualif SplitWith(v:List Data.ByteString.Internal.ByteString, l:Int): ((bLengths v) + (len v) - 1) = l @-}

-- for ByteString.unfoldrN
{-@ qualif PtrDiff(v:Int, i:Int, p:GHC.Ptr.Ptr a): (i - v) <= (plen p) @-}

-- for ByteString.split
{-@ qualif BSValidOff(v:Int,l:Int,p:GHC.ForeignPtr.ForeignPtr a): v + l <= (fplen p) @-}
{-@ qualif SplitLoop(v:List Data.ByteString.Internal.ByteString, l:Int, n:Int): (bLengths v) + (len v) - 1 = l - n @-}
{- qualif SplitWith(v:a, l:Int): ((bLengths v) + (len v) - 1) = l @-}
{- qualif BSValidFP(p:a, o:Int, l:Int): (o + l) <= (fplen p)     @-}
{- qualif BSValidP(p:a, o:Int, l:Int) : (o + l) <= (plen p)       @-}
{- qualif PtrCMP(v:Ptr a, p:Ptr b): (plen v) <= (plen p)                           @-}
{- qualif PtrCMP(v:Ptr a, p:Ptr b): (plen v) >= (plen p)                           @-}
{- qualif SuffixBase(v:a, p:b): ((isNullPtr v) || (pbase v) = (pbase p))           @-}
{- qualif SuffixLenUB(v:a, p:b): ((isNullPtr v) || (plen v) <= (plen p))           @-}
{- qualif SuffixLenLB(v:a, p:b, n:c): ((isNullPtr v) || (plen p) - n  <= (plen v)) @-}

{-@ qualif PtrDiffUnfoldrN(v:int, i:int, p:GHC.Ptr.Ptr a): (i - v) <= (plen p) @-}
{-@ qualif FilterLoop(v:GHC.Ptr.Ptr a, f:GHC.Ptr.Ptr a, t:GHC.Ptr.Ptr a): (plen t) >= (plen f) - (plen v) @-}

{-@ qualif BLengthsAcc(v:List Data.ByteString.Internal.ByteString,
                       c:Data.ByteString.Internal.ByteString,
                       cs:List Data.ByteString.Internal.ByteString):
        (bLengths v) = (bLength c) + (bLengths cs)
  @-}

{-@ qualif BLengthsSum(v:List List a, bs:List Data.ByteString.Internal.ByteString):
       (sumLens v) = (bLengths bs)
  @-}

--LIQUID from ByteString
{-@ mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> b:ByteString -> (acc, ByteStringSZ b) @-}
mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumL = undefined

{-@ mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> b:ByteString -> (acc, ByteStringSZ b) @-}
mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumR = undefined

{-@ group :: b:ByteString -> {v: [ByteStringNE] | (bLengths v) = (bLength b)} @-}
group :: ByteString -> [ByteString]
group = undefined

{-@ groupBy :: (Word8 -> Word8 -> Bool) -> b:ByteString -> {v:[ByteStringNE] | (bLengths v) = (bLength b)} @-}
groupBy :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
groupBy = undefined

{-@ intersperse :: Word8 -> b:ByteString
                -> {v:ByteString |
                     (((bLength b) > 0) ? ((bLength v) = (2 * (bLength b)) - 1)
                                          : ((bLength v) = 0)) }
  @-}
intersperse :: Word8 -> ByteString -> ByteString
intersperse = undefined

{-@ inits :: b:ByteString -> [{v1:ByteString | (bLength v1) <= (bLength b)}]<{\ix iy -> (bLength ix) < (bLength iy)}> @-}
inits :: ByteString -> [ByteString]
inits = undefined

{-@ unfoldrN :: i:Nat -> (a -> Maybe (Word8, a)) -> a -> ({v:ByteString | (bLength v) <= i}, Maybe a)<{\b m -> ((isJust m) => ((bLength b) > 0))}> @-}
unfoldrN :: Int -> (a -> Maybe (Word8, a)) -> a -> (ByteString, Maybe a)
unfoldrN = undefined

{-@ splitAt :: n:Nat
            -> b:ByteString
            -> (ByteString, ByteString)<{\x y ->
                 ((Min (bLength x) (bLength b) n)
                  && ((bLength y) = ((bLength b) - (bLength x))))}>
  @-}
splitAt :: Int -> ByteString -> (ByteString, ByteString)
splitAt = undefined
