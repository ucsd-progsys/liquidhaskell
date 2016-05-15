{-@ LIQUID "--pruneunsorted" @-}
{-@ LIQUID "--notermination" @-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Rank2Types #-}
-- |
-- Module      : Data.Text.Lazy.Encoding
-- Copyright   : (c) 2009, 2010 Bryan O'Sullivan
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : portable
--
-- Functions for converting lazy 'Text' values to and from lazy
-- 'ByteString', using several standard encodings.
--
-- To gain access to a much larger variety of encodings, use the
-- @text-icu@ package: <http://hackage.haskell.org/package/text-icu>

module Data.Text.Lazy.Encoding
    (
    -- * Decoding ByteStrings to Text
    -- $strict
      decodeASCII
    , decodeUtf8
    , decodeUtf16LE
    , decodeUtf16BE
    , decodeUtf32LE
    , decodeUtf32BE

    -- ** Catchable failure
    , decodeUtf8'

    -- ** Controllable error handling
    , decodeUtf8With
    , decodeUtf16LEWith
    , decodeUtf16BEWith
    , decodeUtf32LEWith
    , decodeUtf32BEWith

    -- * Encoding Text to ByteStrings
    , encodeUtf8
    , encodeUtf16LE
    , encodeUtf16BE
    , encodeUtf32LE
    , encodeUtf32BE
    ) where

import Control.Exception (evaluate, try)
import Data.Bits ((.&.))
import Data.Text.Encoding.Error (OnDecodeError, UnicodeException, strictDecode)
import Data.Text.Lazy.Internal (Text(..), chunk, empty, foldrChunks)
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.ByteString as S
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString.Lazy.Internal as B
import qualified Data.ByteString.Unsafe as S
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Lazy.Encoding.Fusion as E
import qualified Data.Text.Lazy.Fusion as F

--LIQUID
import Data.Word (Word8)
import Language.Haskell.Liquid.Prelude

-- $strict
--
-- All of the single-parameter functions for decoding bytestrings
-- encoded in one of the Unicode Transformation Formats (UTF) operate
-- in a /strict/ mode: each will throw an exception if given invalid
-- input.
--
-- Each function has a variant, whose name is suffixed with -'With',
-- that gives greater control over the handling of decoding errors.
-- For instance, 'decodeUtf8' will throw an exception, but
-- 'decodeUtf8With' allows the programmer to determine what to do on a
-- decoding error.

-- | /Deprecated/.  Decode a 'ByteString' containing 7-bit ASCII
-- encoded text.
--
-- This function is deprecated.  Use 'decodeUtf8' instead.
decodeASCII :: B.ByteString -> Text
decodeASCII = decodeUtf8
{-# DEPRECATED decodeASCII "Use decodeUtf8 instead" #-}


--LIQUID FIXME: this is used below in the `slow` case where the
--resulting char is inserted into a new Text with `singleton` so there
--is no Array to pass..
{-@ onErrLIQUID :: OnDecodeError -> String -> Maybe Word8 -> Maybe Char @-}
onErrLIQUID :: TE.OnDecodeError -> String -> Maybe Word8 -> Maybe Char
onErrLIQUID onErr desc c = onErr desc c undefined undefined

-- | Decode a 'ByteString' containing UTF-8 encoded text.
{-@ decodeUtf8With :: OnDecodeError -> B.ByteString -> Text @-}
decodeUtf8With :: TE.OnDecodeError -> B.ByteString -> Text
decodeUtf8With onErr bs0 = fast bs0
  where
    decode = TE.decodeUtf8With onErr
    fast (B.Chunk p ps) | isComplete p = chunk (decode p) (fast ps)
                        | otherwise    = chunk (decode h) (slow t ps)
      where (h,t) = S.splitAt pivot p
            pivot | at 1      = len-1
                  | at 2      = len-2
                  | otherwise = len-3
            len  = S.length p
            --LIQUID at n = len >= n && S.unsafeIndex p (len-n) .&. 0xc0 == 0xc0
            at n = if len >= n then S.unsafeIndex p (len-n) .&. 0xc0 == 0xc0 else False
    fast B.Empty = empty
    slow i bs = {-# SCC "decodeUtf8With'/slow" #-}
                case B.uncons bs of
                  Just (w,bs') | isComplete i' -> chunk (decode i') (fast bs')
                               | otherwise     -> slow i' bs'
                    where i' = S.snoc i w
                  Nothing -> case S.uncons i of
                               Just (j,i') ->
                                 case onErrLIQUID onErr desc (Just j) of
                                   Nothing -> slow i' bs
                                   Just c  -> Chunk (T.singleton c) (slow i' bs)
                               Nothing ->
                                 case onErrLIQUID onErr desc Nothing of
                                   Nothing -> empty
                                   Just c  -> Chunk (T.singleton c) empty
    isComplete bs = {-# SCC "decodeUtf8With'/isComplete" #-}
                    ix 1 .&. 0x80 == 0 ||
                    --LIQUID (len >= 2 && ix 2 .&. 0xe0 == 0xc0) ||
                    --LIQUID (len >= 3 && ix 3 .&. 0xf0 == 0xe0) ||
                    --LIQUID (len >= 4 && ix 4 .&. 0xf8 == 0xf0)
                    (if len >= 2 then ix 2 .&. 0xe0 == 0xc0 else False) ||
                    (if len >= 3 then ix 3 .&. 0xf0 == 0xe0 else False) ||
                    (if len >= 4 then ix 4 .&. 0xf8 == 0xf0 else False)
      where len = S.length bs
            ix n = S.unsafeIndex bs (len-n)
    desc = "Data.Text.Lazy.Encoding.decodeUtf8With: Invalid UTF-8 stream"
{-# INLINE[0] decodeUtf8With #-}

-- | Decode a 'ByteString' containing UTF-8 encoded text that is known
-- to be valid.
--
-- If the input contains any invalid UTF-8 data, an exception will be
-- thrown that cannot be caught in pure code.  For more control over
-- the handling of invalid data, use 'decodeUtf8'' or
-- 'decodeUtf8With'.
decodeUtf8 :: B.ByteString -> Text
decodeUtf8 = decodeUtf8With TE.strictDecode
{-# INLINE[0] decodeUtf8 #-}

-- This rule seems to cause performance loss.
{- RULES "LAZY STREAM stream/decodeUtf8' fusion" [1]
   forall bs. F.stream (decodeUtf8' bs) = E.streamUtf8 strictDecode bs #-}

-- | Decode a 'ByteString' containing UTF-8 encoded text..
--
-- If the input contains any invalid UTF-8 data, the relevant
-- exception will be returned, otherwise the decoded text.
--
-- /Note/: this function is /not/ lazy, as it must decode its entire
-- input before it can return a result.  If you need lazy (streaming)
-- decoding, use 'decodeUtf8With' in lenient mode.
decodeUtf8' :: B.ByteString -> Either UnicodeException Text
decodeUtf8' bs = unsafePerformIO $ do
                   let t = decodeUtf8 bs
                   try (evaluate (rnf t `seq` t))
  where
    rnf Empty        = ()
    rnf (Chunk _ ts) = rnf ts
{-# INLINE decodeUtf8' #-}

encodeUtf8 :: Text -> B.ByteString
encodeUtf8 (Chunk c cs) = B.Chunk (TE.encodeUtf8 c) (encodeUtf8 cs)
encodeUtf8 Empty        = B.Empty

-- | Decode text from little endian UTF-16 encoding.
decodeUtf16LEWith :: OnDecodeError -> B.ByteString -> Text
decodeUtf16LEWith onErr bs = F.unstream (E.streamUtf16LE onErr bs)
{-# INLINE decodeUtf16LEWith #-}

-- | Decode text from little endian UTF-16 encoding.
--
-- If the input contains any invalid little endian UTF-16 data, an
-- exception will be thrown.  For more control over the handling of
-- invalid data, use 'decodeUtf16LEWith'.
decodeUtf16LE :: B.ByteString -> Text
decodeUtf16LE = decodeUtf16LEWith strictDecode
{-# INLINE decodeUtf16LE #-}

-- | Decode text from big endian UTF-16 encoding.
decodeUtf16BEWith :: OnDecodeError -> B.ByteString -> Text
decodeUtf16BEWith onErr bs = F.unstream (E.streamUtf16BE onErr bs)
{-# INLINE decodeUtf16BEWith #-}

-- | Decode text from big endian UTF-16 encoding.
--
-- If the input contains any invalid big endian UTF-16 data, an
-- exception will be thrown.  For more control over the handling of
-- invalid data, use 'decodeUtf16BEWith'.
decodeUtf16BE :: B.ByteString -> Text
decodeUtf16BE = decodeUtf16BEWith strictDecode
{-# INLINE decodeUtf16BE #-}

-- | Encode text using little endian UTF-16 encoding.
encodeUtf16LE :: Text -> B.ByteString
encodeUtf16LE txt = B.fromChunks (foldrChunks (const $ (:) . TE.encodeUtf16LE) [] txt)
{-# INLINE encodeUtf16LE #-}

-- | Encode text using big endian UTF-16 encoding.
encodeUtf16BE :: Text -> B.ByteString
encodeUtf16BE txt = B.fromChunks (foldrChunks (const $ (:) . TE.encodeUtf16BE) [] txt)
{-# INLINE encodeUtf16BE #-}

-- | Decode text from little endian UTF-32 encoding.
decodeUtf32LEWith :: OnDecodeError -> B.ByteString -> Text
decodeUtf32LEWith onErr bs = F.unstream (E.streamUtf32LE onErr bs)
{-# INLINE decodeUtf32LEWith #-}

-- | Decode text from little endian UTF-32 encoding.
--
-- If the input contains any invalid little endian UTF-32 data, an
-- exception will be thrown.  For more control over the handling of
-- invalid data, use 'decodeUtf32LEWith'.
decodeUtf32LE :: B.ByteString -> Text
decodeUtf32LE = decodeUtf32LEWith strictDecode
{-# INLINE decodeUtf32LE #-}

-- | Decode text from big endian UTF-32 encoding.
decodeUtf32BEWith :: OnDecodeError -> B.ByteString -> Text
decodeUtf32BEWith onErr bs = F.unstream (E.streamUtf32BE onErr bs)
{-# INLINE decodeUtf32BEWith #-}

-- | Decode text from big endian UTF-32 encoding.
--
-- If the input contains any invalid big endian UTF-32 data, an
-- exception will be thrown.  For more control over the handling of
-- invalid data, use 'decodeUtf32BEWith'.
decodeUtf32BE :: B.ByteString -> Text
decodeUtf32BE = decodeUtf32BEWith strictDecode
{-# INLINE decodeUtf32BE #-}

-- | Encode text using little endian UTF-32 encoding.
encodeUtf32LE :: Text -> B.ByteString
encodeUtf32LE txt = B.fromChunks (foldrChunks (const $ (:) . TE.encodeUtf32LE) [] txt)
{-# INLINE encodeUtf32LE #-}

-- | Encode text using big endian UTF-32 encoding.
encodeUtf32BE :: Text -> B.ByteString
encodeUtf32BE txt = B.fromChunks (foldrChunks (const $ (:) . TE.encodeUtf32BE) [] txt)
{-# INLINE encodeUtf32BE #-}
