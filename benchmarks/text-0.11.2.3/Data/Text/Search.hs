{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}

-- |
-- Module      : Data.Text.Search
-- Copyright   : (c) Bryan O'Sullivan 2009
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : GHC
--
-- Fast substring search for 'Text', based on work by Boyer, Moore,
-- Horspool, Sunday, and Lundh.
--
-- References:
--
-- * R. S. Boyer, J. S. Moore: A Fast String Searching Algorithm.
--   Communications of the ACM, 20, 10, 762-772 (1977)
--
-- * R. N. Horspool: Practical Fast Searching in Strings.  Software -
--   Practice and Experience 10, 501-506 (1980)
--
-- * D. M. Sunday: A Very Fast Substring Search Algorithm.
--   Communications of the ACM, 33, 8, 132-142 (1990)
--
-- * F. Lundh: The Fast Search Algorithm.
--   <http://effbot.org/zone/stringlib.htm> (2006)

module Data.Text.Search
    (
      indices
    ) where

import qualified Data.Text.Array as A
import Data.Word (Word64)
import Data.Text.Internal (Text(..))
import Data.Bits ((.|.), (.&.))
import Data.Text.UnsafeShift (shiftL)

--LIQUID
import qualified Data.Text.Array
import qualified Data.Word
import Data.Word
import Language.Haskell.Liquid.Prelude

data T = {-# UNPACK #-} !Word64 `T` {-# UNPACK #-} !Int

{-@ measure tskip :: T -> Int
    tskip (T mask skip) = skip
  @-}

--LIQUID FIXME: clean this up so it's readable!!

-- | /O(n+m)/ Find the offsets of all non-overlapping indices of
-- @needle@ within @haystack@.  The offsets returned represent
-- locations in the low-level array.
--
-- In (unlikely) bad cases, this algorithm's complexity degrades
-- towards /O(n*m)/.
{-@ indices :: pat:Data.Text.Internal.Text
            -> src:Data.Text.Internal.Text
            -> [{v:Int | (BtwnI v 0 ((tlen src) - (tlen pat)))}]<{\ix iy ->
                (ix+(tlen pat)) <= iy}>
  @-}
indices :: Text                -- ^ Substring to search for (@needle@)
        -> Text                -- ^ Text to search in (@haystack@)
        -> [Int]
indices _needle@(Text narr noff nlen) _haystack@(Text harr hoff hlen)
    --LIQUID switched first two guards, need to consider whether this is problematic..
    | nlen <= 0 || ldiff < 0 = []
--    | nlen == 1              = scanOne _needle _haystack hindex (nindex 0)
    | nlen == 1              = scanOne _needle _haystack (index _needle 0)
    | otherwise              = scan _needle _haystack 0
  where
    ldiff    = hlen - nlen
    -- nlast    = nlen - 1
    -- z        = nindex nlast
    -- nindex k = A.unsafeIndex narr (noff+k)
    -- hindex k = A.unsafeIndex harr (hoff+k)
    -- hindex' k | k == hlen  = 0
    --           | otherwise = A.unsafeIndex harr (hoff+k)
    -- buildTable !i !msk !skp
    --     | i >= nlast           = (msk .|. swizzle z) :* skp
    --     | otherwise            = buildTable (i+1) (msk .|. swizzle c) skp'
    --     where c                = nindex i
    --           skp' | c == z    = nlen - i - 2
    --                | otherwise = skp
    -- swizzle k = 1 `shiftL` (fromIntegral k .&. 0x3f)
    -- scan !i
    --     | i > ldiff                  = []
    --     | c == z && candidateMatch 0 = i : scan (i + nlen)
    --     | otherwise                  = scan (i + delta)
    --     where c = hindex (i + nlast)
    --           candidateMatch !j
    --                 | j >= nlast               = True
    --                 | hindex (i+j) /= nindex j = False
    --                 | otherwise                = candidateMatch (j+1)
    --           delta | nextInPattern = nlen + 1
    --                 | c == z        = skip + 1
    --                 | otherwise     = 1
    --             where nextInPattern = mask .&. swizzle (hindex' (i+nlen)) == 0
    --           !(mask :* skip)       = buildTable 0 0 (nlen-2)
    -- scanOne c = loop 0
    --     where loop !i | i >= hlen     = []
    --                   | hindex i == c = i : loop (i+1)
    --                   | otherwise     = loop (i+1)
{- INLINE indices #-}

{-@ buildTable :: pat:{v:Data.Text.Internal.Text | (tlen v) > 1}
               -> i:{v:Int | (Btwn v 0 (tlen pat))}
               -> Word64
               -> skp:{v:Int | (Btwn v 0 (tlen pat))}
               -> {v:T | (Btwn (tskip v) 0 (tlen pat))}
  @-}
buildTable :: Text -> Int -> Word64 -> Int -> T
buildTable pat@(Text narr noff nlen) !i !msk !skp
    | i >= nlast           = (msk .|. swizzle z) `T` skp
    | otherwise            = let skp' | c == z    = nlen - i - 2
                                      | otherwise = skp
                             in buildTable pat (i+1) (msk .|. swizzle c) skp'
    where nlast            = nlen - 1
          z                = index pat nlast
          c                = index pat i

swizzle k = 1 `shiftL` (fromIntegral k .&. 0x3f)

{-@ delta :: pat:{v:Data.Text.Internal.Text | (tlen v) > 1}
          -> src:{v:Data.Text.Internal.Text | (tlen v) >= (tlen pat)}
          -> i:{v:Int | (BtwnI v 0 ((tlen src) - (tlen pat)))}
          -> Word16
          -> Word16
          -> {v:Int | (BtwnI v 1 ((tlen pat) + 1))}
  @-}
delta :: Text -> Text -> Int -> Word16 -> Word16 -> Int
delta pat@(Text narr noff nlen) src i c z
    | nextInPattern = nlen + 1
    | c == z        = skip + 1
    | otherwise     = 1
    where nextInPattern = mask .&. swizzle (index' src (i+nlen)) == 0
          !(mask `T` skip)      = buildTable pat 0 0 (nlen-2)


{-@ scan :: pat:{v:Data.Text.Internal.Text | (tlen v) > 1}
         -> src:{v:Data.Text.Internal.Text | (tlen v) >= (tlen pat)}
         -> i:{v:Int | v >= 0}
         -> [{v:Int | (BtwnI (v) (i) ((tlen src) - (tlen pat)))}]<{\ix iy ->
             (ix+(tlen pat)) <= iy}>
  @-}
scan :: Text -> Text -> Int -> [Int]
scan pat@(Text narr noff nlen) src@(Text harr hoff hlen) !i
    | i > ldiff = []
    | otherwise = let nlast = nlen - 1
                      z = index pat nlast
                      c = index src (i + nlast)
                      -- buildTable !i !msk !skp
                      --     | i >= nlast           = (msk .|. swizzle z) :* skp
                      --     | otherwise            = buildTable (i+1) (msk .|. swizzle c) skp'
                      --     where c                = index pat i
                      --           skp' | c == z    = nlen - i - 2
                      --                | otherwise = skp
                      candidateMatch !j
                            | j >= nlast               = True
                            | index src (i+j) /= index pat j = False
                            | otherwise                = candidateMatch (j+1)
                      -- delta | nextInPattern = nlen + 1
                      --       | c == z        = skip + 1
                      --       | otherwise     = 1
                      --   where nextInPattern = mask .&. swizzle (index' src (i+nlen)) == 0
                      -- !(mask `T` skip)      = buildTable pat 0 0 (nlen-2)
                  in if c == z && candidateMatch 0
                     then i : scan pat src (i + nlen)
                     else scan pat src (i + delta pat src i c z)
    where ldiff = hlen - nlen
          -- nlast = nlen - 1
          -- z = index pat nlast
          -- c = index src (i + nlast)
          -- buildTable !i !msk !skp
          --     | i >= nlast           = (msk .|. swizzle z) :* skp
          --     | otherwise            = buildTable (i+1) (msk .|. swizzle c) skp'
          --     where c                = index pat i
          --           skp' | c == z    = nlen - i - 2
          --                | otherwise = skp
          -- candidateMatch !j
          --       | j >= nlast               = True
          --       | index src (i+j) /= index pat j = False
          --       | otherwise                = candidateMatch (j+1)
          -- delta | nextInPattern = nlen + 1
          --       | c == z        = skip + 1
          --       | otherwise     = 1
          --   where nextInPattern = mask .&. swizzle (index' src (i+nlen)) == 0
          -- !(mask :* skip)       = buildTable 0 0 (nlen-2)

{-@ scanOne :: pat:{v:Data.Text.Internal.Text | (tlen v) = 1}
            -> src:{v:Data.Text.Internal.Text | (tlen v) >= (tlen pat)}
            -> Word16
            -> [{v:Int | (Btwn v 0 (tlen src))}]<{\ix iy ->
                (ix+(tlen pat)) <= iy}>
  @-}
scanOne :: Text -> Text -> Word16 -> [Int]
scanOne pat src c = scanOne_loop pat src c 0
    -- where loop !i | i >= hlen     = []
    --               | hindex i == c = i : loop (i+1)
    --               | otherwise     = loop (i+1)

{-@ scanOne_loop :: pat:{v:Data.Text.Internal.Text | (tlen v) = 1}
                 -> src:{v:Data.Text.Internal.Text | (tlen v) >= (tlen pat)}
                 -> Word16
                 -> i:{v:Int | (BtwnI v 0 (tlen src))}
                 -> [{v:Int | (Btwn (v) (i) (tlen src))}]<{\ix iy ->
                     (ix+(tlen pat)) <= iy}>
  @-}
scanOne_loop :: Text -> Text -> Word16 -> Int -> [Int]
scanOne_loop pat src@(Text _ _ hlen) c !i
    | i >= hlen     = []
    | index src i == c = i : scanOne_loop pat src c (i+1)
    | otherwise     = scanOne_loop pat src c (i+1)


{-@ index :: t:Data.Text.Internal.Text
          -> k:{v:Int | (Btwn v 0 (tlen t))}
          -> Word16
  @-}
index :: Text -> Int -> Word16
index (Text arr off len) k = A.unsafeIndex arr (off+k)

{-@ index' :: t:Data.Text.Internal.Text
           -> k:{v:Int | (BtwnI v 0 (tlen t))}
           -> Word16
  @-}
index' (Text arr off len) k
    | k == len  = 0
    | otherwise = A.unsafeIndex arr (off+k)








