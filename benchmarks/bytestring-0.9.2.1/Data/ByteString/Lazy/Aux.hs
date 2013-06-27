module Data.ByteString.Lazy.Aux where

import Data.ByteString.Internal
import Data.Word

{-@ qualif BLengthsAcc(v:List Data.ByteString.Internal.ByteString,
                       c:Data.ByteString.Internal.ByteString,
                       cs:List Data.ByteString.Internal.ByteString):
        (bLengths v) = (bLength c) + (bLengths cs)
  @-}

{-@ qualif BLengthsSum(v:List List a, bs:List Data.ByteString.Internal.ByteString):
       (sumLens v) = (bLengths bs)
  @-}

{-@ qualif BLenLE(v:Data.ByteString.Internal.ByteString, n:int): (bLength v) <= n @-}
{-@ qualif BLenEq(v:Data.ByteString.Internal.ByteString,
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
