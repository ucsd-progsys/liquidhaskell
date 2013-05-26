{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}
module Data.Text.Lazy.SearchAux where

import qualified Data.Text.Array as A
import Data.Int (Int64)
import Data.Word (Word16, Word64)
import qualified Data.Text.Internal as T
import Data.Text.Fusion.Internal (PairS(..))
import Data.Text.Lazy.Internal (Text(..), foldlChunks)
import Data.Bits ((.|.), (.&.))
import Data.Text.UnsafeShift (shiftL)

--LIQUID
import qualified Data.Text.Array
import qualified Data.Text.Fusion.Internal
import qualified Data.Text.Internal
import Data.Text.Lazy.Internal (foldrChunks)
import qualified Data.Word
import Data.Int (Int32)
import Language.Haskell.Liquid.Prelude


{-@ lackingHay :: q:{v:Int64 | v >= 0}
               -> t:NonEmptyStrict
               -> ts:Data.Text.Lazy.Internal.Text
               -> {v:Bool | ((Prop v) <=> (q > ((tlen t) + (ltlen ts))))}
  @-}
lackingHay :: Int64 -> T.Text -> Text -> Bool
lackingHay q t ts = lackingHay_go q 0 t ts

{-@ lackingHay_go :: q:{v:Int64 | v >= 0}
               -> p:{v:Int64 | v >= 0}
               -> t:NonEmptyStrict
               -> ts:Data.Text.Lazy.Internal.Text
               -> {v:Bool | ((Prop v) <=> (q > (p + (tlen t) + (ltlen ts))))}
  @-}
lackingHay_go :: Int64 -> Int64 -> T.Text -> Text -> Bool
lackingHay_go q p (T.Text _ _ l) Empty = q > (p + fromIntegral l)
lackingHay_go q p (T.Text _ _ l) (Chunk r rs) = let p' = p + fromIntegral l
                                                in q > p' && lackingHay_go q p' r rs

{-@ buildTable :: Word16
               -> nlen:{v:Int64 | v > 1}
               -> ts0:{v:Data.Text.Lazy.Internal.Text | (BtwnI (ltlen v) 0 nlen)}
               -> t:{v:Data.Text.Internal.Text | (BtwnEI (tlen v) 0 nlen)}
               -> ts:{v:Data.Text.Lazy.Internal.Text |
                         (((ltlen v) + (tlen t)) = (nlen - (ltlen ts0)))}
               -> i:{v:Int | (Btwn v 0 (tlen t))}
               -> g:{v:Int64 | (BtwnI v 0 ((ltlen ts0) + i))}
               -> Word64
               -> {v:Int64 | (Btwn (v) (0) nlen)}
               -> PairS Word64 {v:Int64 | (Btwn (v) (0) nlen)}
  @-}
buildTable :: Word16 -> Int64 -> Text -> T.Text -> Text -> Int -> Int64 -> Word64 -> Int64
           -> PairS Word64 Int64
buildTable z nlen ts0 t@(T.Text xarr xoff xlen) xs !i !(g::Int64) !msk !skp =
    if i >= xlast then case xs of
                         Empty      -> (msk .|. swizzle z) :*: skp
                         Chunk y ys -> let msk'             = msk .|. swizzle c
                                           skp' | c == z    = nlen - g - 2
                                                | otherwise = skp
                                       in buildTable z nlen (Chunk t ts0) y ys 0 g msk' skp'
    else let msk'             = msk .|. swizzle c
             skp' | c == z    = nlen - g - 2
                  | otherwise = skp
         in buildTable z nlen ts0 t xs (i+1) (g+1) msk' skp'
  where c = A.unsafeIndex xarr (xoff+i)
        xlast = xlen - 1

swizzle w = 1 `shiftL` (fromIntegral w .&. 0x3f)

