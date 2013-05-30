{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}

-- |
-- Module      : Data.Text.Lazy.Search
-- Copyright   : (c) 2009, 2010 Bryan O'Sullivan
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : GHC
--
-- Fast substring search for lazy 'Text', based on work by Boyer,
-- Moore, Horspool, Sunday, and Lundh.  Adapted from the strict
-- implementation.

module Data.Text.Lazy.Search
    (
      indices
    ) where

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


-- | /O(n+m)/ Find the offsets of all non-overlapping indices of
-- @needle@ within @haystack@.
--
-- This function is strict in @needle@, and lazy (as far as possible)
-- in the chunks of @haystack@.
--
-- In (unlikely) bad cases, this algorithm's complexity degrades
-- towards /O(n*m)/.
{-@ indices :: pat:Data.Text.Lazy.Internal.Text
            -> src:Data.Text.Lazy.Internal.Text
            -> [{v:Int64 | (BtwnI v 0 ((ltlen src) - (ltlen pat)))}]<{\ix iy ->
                (ix+(ltlen pat)) <= iy}>
  @-}
indices :: Text              -- ^ Substring to search for (@needle@)
        -> Text              -- ^ Text to search in (@haystack@)
        -> [Int64]
indices needle@(Chunk n ns) _haystack@(Chunk k ks) =
    if      nlen <= 0 then []
    else if nlen == 1 then indicesOne (nindex 0) _haystack Empty k ks 0
    else advance needle _haystack Empty k ks 0 0
  where
    -- advance x@(T.Text _ _ l) xs = scan
    --  where
    --   scan !g !i
    --      | i >= m = case xs of
    --                   Empty           -> []
    --                   Chunk y ys      -> advance y ys g (i-m)
    --      | lackingHay (i + nlen) x xs  = []
    --      | c == z && candidateMatch 0  = g : scan (g+nlen) (i+nlen)
    --      | otherwise                   = scan (g+delta) (i+delta)
    --    where
    --      m = fromIntegral l
    --      c = hindex (i + nlast)
    --      delta | nextInPattern = nlen + 1
    --            | c == z        = skip + 1
    --            | otherwise     = 1
    --      nextInPattern         = mask .&. swizzle (hindex (i+nlen)) == 0
    --      candidateMatch !j
    --          | j >= nlast               = True
    --          | hindex (i+j) /= nindex j = False
    --          | otherwise                = candidateMatch (j+1)
    --      hindex                         = index x xs
    nlen      = wordLength needle
    nlast     = nlen - 1
    nindex    = index n ns
    -- z         = foldlChunks fin 0 needle
    --             --LIQUID fin param needs to be non-empty
    --     where fin _ (T.Text farr foff flen) = A.unsafeIndex farr (foff+flen-1)
    -- (mask :: Word64) :*: skip = buildTable n ns 0 0 0 (nlen-2)
    -- swizzle w = 1 `shiftL` (fromIntegral w .&. 0x3f)
    -- buildTable (T.Text xarr xoff xlen) xs = go
    --   where
    --     go !(g::Int64) !i !msk !skp
    --         | i >= xlast = case xs of
    --                          Empty      -> (msk .|. swizzle z) :*: skp
    --                          Chunk y ys -> buildTable y ys g 0 msk' skp'
    --         | otherwise = go (g+1) (i+1) msk' skp'
    --         where c                = A.unsafeIndex xarr (xoff+i)
    --               msk'             = msk .|. swizzle c
    --               skp' | c == z    = nlen - g - 2
    --                    | otherwise = skp
    --               xlast = xlen - 1
    -- -- | Check whether an attempt to index into the haystack at the
    -- -- given offset would fail.
    -- lackingHay q = go 0
    --   where
    --     go p (T.Text _ _ l) ps = p' < q && case ps of
    --                                          Empty      -> True
    --                                          Chunk r rs -> go p' r rs
    --         where p' = p + fromIntegral l
indices _ _ = []

{-@ advance :: pat:{v:Data.Text.Lazy.Internal.Text | (ltlen v) > 1}
            -> src:{v:Data.Text.Lazy.Internal.Text | (ltlen v) > 0}
            -> ts0:{v:Data.Text.Lazy.Internal.Text | (ltlen v) <= (ltlen src)}
            -> x:{v:Data.Text.Internal.Text | (BtwnEI (tlen v) 0 (ltlen src))}
            -> xs:{v:Data.Text.Lazy.Internal.Text |
                   (((ltlen v) + (tlen x)) = ((ltlen src) - (ltlen ts0)))}
            -> i:{v:Int64 | v >= 0}
            -> g:{v:Int64 | (v - i) = (ltlen ts0)}
            -> [{v:Int64 | (BtwnI (v) (g) ((ltlen src) - (ltlen pat)))}]<{\ix iy ->
                (ix+(ltlen pat)) <= iy}>
  @-}
advance :: Text -> Text -> Text -> T.Text -> Text -> Int64 -> Int64 -> [Int64]
advance needle t0 ts0 x xs g i = advance_scan needle t0 ts0 x xs g i


{-@ advance_scan :: pat:{v:Data.Text.Lazy.Internal.Text | (ltlen v) > 1}
            -> src:{v:Data.Text.Lazy.Internal.Text | (ltlen v) > 0}
            -> ts0:{v:Data.Text.Lazy.Internal.Text | (ltlen v) <= (ltlen src)}
            -> x:{v:Data.Text.Internal.Text | (BtwnEI (tlen v) 0 (ltlen src))}
            -> xs:{v:Data.Text.Lazy.Internal.Text |
                   (((ltlen v) + (tlen x)) = ((ltlen src) - (ltlen ts0)))}
            -> i:{v:Int64 | v >= 0}
            -> g:{v:Int64 | (v - i) = (ltlen ts0)}
            -> [{v:Int64 | (BtwnI (v) (g) ((ltlen src) - (ltlen pat)))}]<{\ix iy ->
                (ix+(ltlen pat)) <= iy}>
  @-}
advance_scan :: Text -> Text -> Text -> T.Text -> Text -> Int64 -> Int64 -> [Int64]
advance_scan needle@(Chunk n ns) src ts0 x@(T.Text _ _ l) xs !i !g =
  if i >= m then case xs of
                   Empty           -> []
                   Chunk y ys      -> advance needle src (Chunk x ts0) y ys (i-m) g
  else if lackingHay (i + nlen) x xs  then []
  else let d = delta nlen skip c z nextInPattern
           c = index x xs (i + nlast)
           nextInPattern = mask .&. swizzle (index x xs (i+nlen)) == 0
           candidateMatch !j
               | j >= nlast               = True
               | index x xs (i+j) /= index n ns j = False
               | otherwise                = candidateMatch (j+1)
       in if c == z && candidateMatch 0
          then g : advance_scan needle src ts0 x xs (i+nlen) (g+nlen)
          else  advance_scan needle src ts0 x xs (i+d) (g+d)
 where
   nlen  = wordLength needle
   nlast = nlen - 1
   (mask :: Word64) :*: skip = buildTable z nlen Empty n ns 0 0 0 (nlen-2)
   z = foldlChunks fin 0 needle
         where fin _ (T.Text farr foff flen) = A.unsafeIndex farr (foff+flen-1)
   m = fromIntegral l


-- | Check whether an attempt to index into the haystack at the
-- given offset would fail.
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


{-@ delta :: nlen:{v:Int64 | v > 1}
          -> skip:{v:Int64 | (BtwnI v 0 nlen)}
          -> Word16
          -> Word16
          -> Bool
          -> {v:Int64 | (BtwnI v 1 (nlen + 1))}
  @-}
delta :: Int64 -> Int64 -> Word16 -> Word16 -> Bool -> Int64
delta nlen skip c z nextInPattern =
    if nextInPattern then nlen + 1
    else if c == z   then skip + 1
    else 1


swizzle w = 1 `shiftL` (fromIntegral w .&. 0x3f)

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


-- | Fast index into a partly unpacked 'Text'.  We take into account
-- the possibility that the caller might try to access one element
-- past the end.
{-@ index :: t:{v:Data.Text.Internal.Text | (tlen v) > 0}
          -> ts:Data.Text.Lazy.Internal.Text
          -> i:{v:Int64 | (BtwnI v 0 ((tlen t) + (ltlen ts)))}
          -> Word16
  @-}
index :: T.Text -> Text -> Int64 -> Word16
index (T.Text arr off len) xs !i =
    if j < len then A.unsafeIndex arr (off+j)
    else case xs of
           Empty ->
                 -- out of bounds, but legal
               if j == len then 0
                 -- should never happen, due to lackingHay above
               else liquidError "index"
           Chunk c cs -> index c cs (i-fromIntegral len)
    where j = fromIntegral i

-- | A variant of 'indices' that scans linearly for a single 'Word16'.
{-@ indicesOne :: Word16
               -> t0:Data.Text.Lazy.Internal.Text
               -> ts0:{v:Data.Text.Lazy.Internal.Text | (ltlen v) <= (ltlen t0)}
               -> t:{v:Data.Text.Internal.Text | (tlen v) > 0}
               -> ts:{v:Data.Text.Lazy.Internal.Text |
                      (((ltlen v) + (tlen t)) = ((ltlen t0) - (ltlen ts0)))}
               -> i:{v:Int64 | v = (ltlen ts0)}
               -> [{v:Int64 | (Btwn (v) (i) (ltlen t0))}]<{\ix iy -> ix < iy}>
  @-}
indicesOne :: Word16 -> Text -> Text -> T.Text -> Text -> Int64 -> [Int64]
--LIQUID indicesOne c = chunk
--LIQUID   where
--LIQUID     chunk !i (T.Text oarr ooff olen) os = go 0
--LIQUID       where
--LIQUID         go h | h >= olen = case os of
--LIQUID                              Empty      -> []
--LIQUID                              Chunk y ys -> chunk (i+fromIntegral olen) y ys
--LIQUID              | on == c = i + fromIntegral h : go (h+1)
--LIQUID              | otherwise = go (h+1)
--LIQUID              where on = A.unsafeIndex oarr (ooff+h)
indicesOne c t0 ts0 t os !i = indicesOne_go c t0 ts0 t os i 0

{-@ indicesOne_go :: Word16
                  -> t0:Data.Text.Lazy.Internal.Text
                  -> ts0:{v:Data.Text.Lazy.Internal.Text | (ltlen v) <= (ltlen t0)}
                  -> t:{v:Data.Text.Internal.Text | (BtwnEI (tlen v) 0 (ltlen t0))}
                  -> ts:{v:Data.Text.Lazy.Internal.Text |
                         (((ltlen v) + (tlen t)) = ((ltlen t0) - (ltlen ts0)))}
                  -> i:{v:Int64 | v = (ltlen ts0)}
                  -> h:{v:Int | (BtwnI v 0 (tlen t))}
                  -> [{v:Int64 | (Btwn (v) (i+h) (ltlen t0))}]<{\ix iy -> ix < iy}>
  @-}
indicesOne_go :: Word16 -> Text -> Text -> T.Text -> Text -> Int64 -> Int -> [Int64]
indicesOne_go c t0 ts0 t@(T.Text oarr ooff olen) os !i h =
    if h >= olen then case os of
                        Empty      -> []
                        Chunk y@(T.Text _ _ l) ys ->
                            indicesOne c t0 (Chunk t ts0) y ys (i+fromIntegral olen)
    else let on = A.unsafeIndex oarr (ooff+h)
         in if on == c
            then i + fromIntegral h : indicesOne_go c t0 ts0 t os i (h+1)
            else indicesOne_go c t0 ts0 t os i (h+1)


-- | The number of 'Word16' values in a 'Text'.
{-@ wordLength :: t:Data.Text.Lazy.Internal.Text
               -> {v:Int64 | v = (ltlen t)}
  @-}
wordLength :: Text -> Int64
--LIQUID wordLength = foldlChunks sumLength 0
--LIQUID     where sumLength i (T.Text _ _ l) = i + fromIntegral l
wordLength = foldrChunks sumLength 0

{-@ sumLength :: ts:Data.Text.Lazy.Internal.Text
              -> t:Data.Text.Internal.Text
              -> i:Int64
              -> {v:Int64 | v = ((tlen t) + i)}
  @-}
sumLength :: Text -> T.Text -> Int64 -> Int64
sumLength _ (T.Text _ _ l) i = i + fromIntegral l

--LIQUID emptyError :: String -> a
--LIQUID emptyError fun = error ("Data.Text.Lazy.Search." ++ fun ++ ": empty input")

















