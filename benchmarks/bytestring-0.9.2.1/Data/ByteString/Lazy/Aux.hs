module Data.ByteString.Lazy.Aux where

import Data.ByteString.Internal
import Data.Word

--LIQUID FIXME: stronger specs than we have currently proven in ByteString

--LIQUID the mapAccum[LR] specs are necessary for proving the lazy
--invariant, but we need specs for the *EFL functions in Fusion.hs to
--prove these specs

{-@ mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> b:ByteString -> (acc, ByteStringSZ b) @-}
mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumL = undefined

{-@ mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> b:ByteString -> (acc, ByteStringSZ b) @-}
mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumR = undefined

--LIQUID the unfoldrN spec is also necessary for proving the lazy invariant
{-@ unfoldrN :: i:Nat -> (a -> Maybe (Word8, a)) -> a -> ({v:ByteString | (bLength v) <= i}, Maybe a)<{\b m -> ((isJust m) => ((bLength b) > 0))}> @-}
unfoldrN :: Int -> (a -> Maybe (Word8, a)) -> a -> (ByteString, Maybe a)
unfoldrN = undefined
