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
    --LIQUID
    , T(..)
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

--LIQUID FIXME: we don't currently parse the `:*` syntax used originally
data T = {-# UNPACK #-} !Word64 `T` {-# UNPACK #-} !Int

{-@ measure tskip :: Data.Text.Search.T -> Int
    tskip (Data.Text.Search.T mask skip) = skip
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
            -> [{v:Nat | v <= ((tlen src) - (tlen pat))}]<{\ix iy ->
                (ix+(tlen pat)) <= iy}>
  @-}
indices :: Text                -- ^ Substring to search for (@needle@)
        -> Text                -- ^ Text to search in (@haystack@)
        -> [Int]
indices _needle@(Text narr noff nlen) _haystack@(Text harr hoff hlen)
    --LIQUID switched first two guards, need to consider whether this is problematic..
    = if      nlen <= 0 || ldiff < 0 then []
      else if nlen == 1              then scanOne (index _needle 0)
      else
        --LIQUID pushing definitions in to prove safety!
        let scan !i
              = if i > ldiff then []
                else
                  let nlast = nlen - 1
                      z     = index _needle nlast
                      c = index _haystack (i + nlast)
                      candidateMatch !j
                          = if j >= nlast               then True
                            else if index _haystack (i+j) /= index _needle j then False
                            else candidateMatch (j+1)
                      delta = if nextInPattern then nlen + 1
                              else if c == z   then skip + 1
                              else 1
                            where nextInPattern = mask .&. swizzle (index' _haystack (i+nlen)) == 0
                                  !(mask `T` skip)       = buildTable _needle 0 0 (nlen-2)
                   in if c == z && candidateMatch 0 then i : scan (i + nlen)
                      else                               scan (i + delta)
        in scan 0
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
    scanOne c = loop 0
        where loop !i = if i >= hlen     then []
                        else if index _haystack i == c then i : loop (i+1)
                        else loop (i+1)
{- INLINE indices #-}

{-@ buildTable :: pat:{v:Data.Text.Internal.Text | (tlen v) > 1}
               -> i:{v:Nat | v < (tlen pat)}
               -> Word64
               -> skp:{v:Nat | v < (tlen pat)}
               -> {v:Data.Text.Search.T | (Btwn (tskip v) 0 (tlen pat))}
  @-}
buildTable :: Text -> Int -> Word64 -> Int -> T
buildTable pat@(Text narr noff nlen) !i !msk !skp
    = if i >= nlast          then (msk .|. swizzle z) `T` skp
      else                   let skp' = if c == z    then nlen - i - 2
                                        else skp
                             in buildTable pat (i+1) (msk .|. swizzle c) skp'
    where nlast            = nlen - 1
          z                = index pat nlast
          c                = index pat i

swizzle k = 1 `shiftL` (fromIntegral k .&. 0x3f)

{-@ index :: t:Data.Text.Internal.Text
          -> k:{v:Nat | v < (tlen t)}
          -> Word16
  @-}
index :: Text -> Int -> Word16
index (Text arr off len) k = A.unsafeIndex arr (off+k)

{-@ index' :: t:Data.Text.Internal.Text
           -> k:{v:Nat | v <= (tlen t)}
           -> Word16
  @-}
index' (Text arr off len) k
    = if k == len then 0
      else A.unsafeIndex arr (off+k)








