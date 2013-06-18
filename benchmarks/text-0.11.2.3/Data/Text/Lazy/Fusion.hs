{-# LANGUAGE BangPatterns #-}
-- |
-- Module      : Data.Text.Lazy.Fusion
-- Copyright   : (c) 2009, 2010 Bryan O'Sullivan
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : GHC
--
-- Core stream fusion functionality for text.

module Data.Text.Lazy.Fusion
    (
      stream
    , unstream
    , unstreamChunks
    , length
    , unfoldrN
    , index
    , countChar
    ) where

import Prelude hiding (length)
import qualified Data.Text.Fusion.Common as S
import Data.Text.Fusion.Internal
import Data.Text.Fusion.Size (isEmpty, unknownSize)
import Data.Text.Lazy.Internal
import qualified Data.Text.Internal as I
import qualified Data.Text.Array as A
import Data.Text.UnsafeChar (unsafeWrite)
import Data.Text.UnsafeShift (shiftL)
import Data.Text.Unsafe (Iter(..), iter)
import Data.Int (Int64)

--LIQUID
import Data.Int (Int32)
import qualified Data.Text
import qualified Data.Text.Array
import qualified Data.Text.Fusion.Internal
import qualified Data.Text.Fusion.Size
import qualified Data.Text.Internal
import qualified Data.Text.Lazy.Internal
import qualified Data.Text.Private
import qualified Data.Text.Search
import qualified Data.Text.Unsafe
import qualified Data.Word
import qualified GHC.ST
import Language.Haskell.Liquid.Prelude

default(Int64)

-- | /O(n)/ Convert a 'Text' into a 'Stream Char'.
stream :: Text -> Stream Char
stream text = Stream next (text :*: 0) unknownSize
  where
    next (Empty :*: _) = Done
    next (txt@(Chunk t@(I.Text _ _ len) ts) :*: i)
        | i >= len  = next (ts :*: 0)
        | otherwise = let Iter c d = iter t i
                      in Yield c (txt :*: i+d)
        --LIQUID push binding inward for safety
        --LIQUID where Iter c d = iter t i
{-# INLINE [0] stream #-}

data UC s = UC s {-# UNPACK #-} !Int

{-@ data Data.Text.Lazy.Fusion.UC s = Data.Text.Lazy.Fusion.UC
        (s :: s)
        (i :: {v:Int | v > 0})
  @-}

{-@ measure ucInt :: Data.Text.Lazy.Fusion.UC s -> Int
    ucInt (Data.Text.Lazy.Fusion.UC s i) = i
  @-}

-- | /O(n)/ Convert a 'Stream Char' into a 'Text', using the given
-- chunk size.
unstreamChunks :: Int -> Stream Char -> Text
unstreamChunks chunkSize (Stream next s0 len0)
  | isEmpty len0 = Empty
  | otherwise    = outer s0
  where
    outer s = {-# SCC "unstreamChunks/outer" #-}
              case next s of
                Done       -> Empty
                Skip s'    -> outer s'
                              --LIQUID the `liquidAssume` is just propagating the type of `i` below in `inner`
                Yield x s' -> I.Text arr 0 (liquidAssume (len <= A.aLen arr) len) `Chunk` outer s''
                  where (arr, UC s'' len) = A.run2 fill
                        fill = do a <- A.new unknownLength
                                  unsafeWrite a 0 x >>= inner a unknownLength s'
                        unknownLength = 4
    inner marr len s !i
        | i + 1 >= chunkSize = return (marr, UC s i)
        | i + 1 >= len       = {-# SCC "unstreamChunks/resize" #-} do
            let newLen = min (len * 2) chunkSize --LIQUID min (len `shiftL` 1) chunkSize
            marr' <- A.new newLen
            A.copyM marr' 0 marr 0 len
            inner marr' newLen s i
        | otherwise =
            {-# SCC "unstreamChunks/inner" #-}
            case next s of
              Done        -> return (marr, UC s i)
              Skip s'     -> inner marr len s' i
              Yield x s'  -> do d <- unsafeWrite marr i x
                                inner marr len s' (i+d)
{-# INLINE [0] unstreamChunks #-}

-- | /O(n)/ Convert a 'Stream Char' into a 'Text', using
-- 'defaultChunkSize'.
unstream :: Stream Char -> Text
unstream = unstreamChunks defaultChunkSize
{-# INLINE [0] unstream #-}

-- | /O(n)/ Returns the number of characters in a text.
length :: Stream Char -> Int64
length = S.lengthI
{-# INLINE[0] length #-}

{-# RULES "LAZY STREAM stream/unstream fusion" forall s.
    stream (unstream s) = s #-}

-- | /O(n)/ Like 'unfoldr', 'unfoldrN' builds a stream from a seed
-- value. However, the length of the result is limited by the
-- first argument to 'unfoldrN'. This function is more efficient than
-- 'unfoldr' when the length of the result is known.
unfoldrN :: Int64 -> (a -> Maybe (Char,a)) -> a -> Stream Char
unfoldrN n = S.unfoldrNI n
{-# INLINE [0] unfoldrN #-}

-- | /O(n)/ stream index (subscript) operator, starting from 0.
index :: Stream Char -> Int64 -> Char
index = S.indexI
{-# INLINE [0] index #-}

-- | /O(n)/ The 'count' function returns the number of times the query
-- element appears in the given stream.
countChar :: Char -> Stream Char -> Int64
countChar = S.countCharI
{-# INLINE [0] countChar #-}
