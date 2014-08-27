{-@ LIQUID "--idirs=../../../bytestring-0.9.2.1/" @-}
{-@ LIQUID "--idirs=../../../../include/" @-}
{-@ LIQUID "--c-files=../../cbits/cbits.c" @-}

{-# LANGUAGE BangPatterns, CPP, ForeignFunctionInterface, MagicHash,
    UnliftedFFITypes #-}
{-# LANGUAGE PackageImports, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
-- Module      : Data.Text.Encoding
-- Copyright   : (c) 2009, 2010, 2011 Bryan O'Sullivan,
--               (c) 2009 Duncan Coutts,
--               (c) 2008, 2009 Tom Harper
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : portable
--
-- Functions for converting 'Text' values to and from 'ByteString',
-- using several standard encodings.
--
-- To gain access to a much larger family of encodings, use the
-- @text-icu@ package: <http://hackage.haskell.org/package/text-icu>

module Data.Text.Encoding
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
    --LIQUID
    , OnDecodeError
    , strictDecode
    ) where

import Control.Exception (evaluate, try)
#if __GLASGOW_HASKELL__ >= 702
import Control.Monad.ST.Unsafe (unsafeIOToST, unsafeSTToIO)
#else
import Control.Monad.ST (unsafeIOToST, unsafeSTToIO)
#endif
import Data.Bits ((.&.))
import Data.ByteString as B
import Data.ByteString.Internal as B
--LIQUID import Data.Text.Encoding.Error (OnDecodeError, UnicodeException, strictDecode)
import Data.Text.Encoding.Error (UnicodeException)
import Data.Text.Internal (Text(..))
import Data.Text.Private (runText)
import Data.Text.UnsafeChar (ord, unsafeWrite)
import Data.Text.UnsafeShift (shiftL, shiftR)
import Data.Word (Word8)
import Foreign.C.Types (CSize)
import Foreign.ForeignPtr (withForeignPtr)
import Foreign.Marshal.Utils (with)
import Foreign.Ptr (Ptr, minusPtr, plusPtr)
import Foreign.Storable (peek, poke)
import GHC.Base (MutableByteArray#)
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Text.Array as A
import qualified Data.Text.Encoding.Fusion as E
import qualified Data.Text.Encoding.Utf16 as U16
import qualified Data.Text.Fusion as F

--LIQUID
import Control.Exception (throw)
import qualified Data.Text.Encoding.Error as E
import Foreign.ForeignPtr (ForeignPtr)
import Language.Haskell.Liquid.Prelude
import Language.Haskell.Liquid.Foreign

{-@ qualif PValid(v:Ptr int, a:A.MArray s):
        (((deref v) >= 0) && ((deref v) < (malen a)))
  @-}
{-@ qualif PLenCmp(v:Ptr a, p:Ptr b): (plen v) >= (plen p) @-}
{-@ qualif PLenCmp(v:Ptr a, p:Ptr b): (plen p) >= (plen v) @-}
{-@ qualif PBaseEq(v:Ptr a, p:Ptr b): (pbase v) = (pbase p) @-}

{-@ type PtrGE N = {v:Ptr Word8 | (plen v) >= N} @-}

{- Foreign.Marshal.Utils.with :: (Storable a)
                               => a:a
                               -> ({v:PtrV a | (deref v) = a} -> IO b)
                               -> IO b
  @-}
--LIQUID FIXME: this is a hacky, specialized type
{-@ withLIQUID :: z:CSize
               -> a:A.MArray s
               -> ({v:Ptr CSize | (Btwn (deref v) z (malen a)) && plen v > 0} -> IO b)
               -> IO b
  @-}
withLIQUID :: CSize -> A.MArray s -> (Ptr CSize -> IO b) -> IO b
withLIQUID = undefined

{-@ qualif EqFPlen(v:ForeignPtr a, n:int): (fplen v) = n @-}

{-@ plen :: p:Ptr a -> {v:Nat | v = (plen p)} @-}
plen :: Ptr a -> Int
plen = undefined

--LIQUID specialize the generic error handler to talk about the array
{-@ type OnDecodeError = forall s.
                         String
                      -> Maybe Word8
                      -> a:A.MArray s
                      -> i:Nat
                      -> Maybe {v:Char | (Room a i v)}
  @-}
type OnDecodeError = forall s. String -> Maybe Word8 -> A.MArray s -> Int -> Maybe Char

{-@ strictDecode :: OnDecodeError @-}
strictDecode :: OnDecodeError
strictDecode desc c _ _ = throw (E.DecodeError desc c)

{-@ qualif Ensure(v:ForeignPtr a, x:int): x <= (fplen v) @-}
{-@ qualif Ensure(v:Ptr a, x:int, y:int): x+y <= (plen v) @-}

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
decodeASCII :: ByteString -> Text
decodeASCII = decodeUtf8
{-# DEPRECATED decodeASCII "Use decodeUtf8 instead" #-}

-- | Decode a 'ByteString' containing UTF-8 encoded text.
{-@ decodeUtf8With :: OnDecodeError -> ByteString -> Text @-}
decodeUtf8With :: OnDecodeError -> ByteString -> Text
decodeUtf8With onErr (PS fp off len) = runText $ \done -> do
  let go dest = withForeignPtr fp $ \ptr ->
        withLIQUID (0::CSize) dest $ \destOffPtr -> do
          let end = ptr `plusPtr` (off + len) :: Ptr Word8
              {- LIQUID WITNESS -}
              loop (d :: Int) curPtr = do
                curPtr' <- c_decode_utf8 dest {-LIQUID (A.maBA dest)-} destOffPtr curPtr end
                if eqPtr curPtr' end --LQIUID SPECIALIZE curPtr' == end
                  then do
                    n <- peek destOffPtr
                    unsafeSTToIO (done dest (fromIntegral n))
                  else do
                    x <- peek curPtr'
                    --LIQUID SCOPE
                    destOff <- peek destOffPtr
                    case onErr desc (Just x) dest (fromIntegral destOff) of
                      Nothing -> loop (plen $ curPtr' `plusPtr` 1) $ curPtr' `plusPtr` 1
                      Just c -> do
                        --LIQUID destOff <- peek destOffPtr
                        w <- unsafeSTToIO $
                             unsafeWrite dest (fromIntegral destOff) c
                        poke destOffPtr (destOff + fromIntegral w)
                        loop (plen $ curPtr' `plusPtr` 1) $ curPtr' `plusPtr` 1
          loop (plen $ ptr `plusPtr` off) (ptr `plusPtr` off)
  (unsafeIOToST . go) =<< A.new len
 where
  desc = "Data.Text.Encoding.decodeUtf8: Invalid UTF-8 stream"
{- INLINE[0] decodeUtf8With #-}

-- | Decode a 'ByteString' containing UTF-8 encoded text that is known
-- to be valid.
--
-- If the input contains any invalid UTF-8 data, an exception will be
-- thrown that cannot be caught in pure code.  For more control over
-- the handling of invalid data, use 'decodeUtf8'' or
-- 'decodeUtf8With'.
decodeUtf8 :: ByteString -> Text
decodeUtf8 = decodeUtf8With strictDecode
{-# INLINE[0] decodeUtf8 #-}
{- RULES "STREAM stream/decodeUtf8 fusion" [1]
    forall bs. F.stream (decodeUtf8 bs) = E.streamUtf8 strictDecode bs #-}

-- | Decode a 'ByteString' containing UTF-8 encoded text..
--
-- If the input contains any invalid UTF-8 data, the relevant
-- exception will be returned, otherwise the decoded text.
decodeUtf8' :: ByteString -> Either UnicodeException Text
decodeUtf8' = unsafePerformIO . try . evaluate . decodeUtf8With strictDecode
{-# INLINE decodeUtf8' #-}

--LIQUID this qualifer is super expensive, so we added the liquidAssume below
{- qualif GE(v:int, o:int, x:int): v >= (o-x) @-}
{-@ qualif PlenEq(v:Ptr a, p:Ptr b): (plen v) = (plen p) @-}

-- | Encode text using UTF-8 encoding.
{-@ Lazy encodeUtf8 @-}
{-@ encodeUtf8 :: t:Text -> {v:ByteString | (((tlen t) > 0) => ((bLength v) > 0))} @-}
encodeUtf8 :: Text -> ByteString
encodeUtf8 (Text arr off len) = unsafePerformIO $ do
  let size0 = max len 4
  mallocByteString size0 >>= start size0 off 0
 where
  offLen = off + len
  start size n0 m0 fp = withForeignPtr fp $ loop n0 m0
   where
    loop n1 m1 ptr = go (offLen-n1) n1 m1
     where
      --LIQUID SCOPE offLen = off + len
       {- LIQUID WITNESS -}
      go (d :: Int) !n !m' = let m = liquidAssume (m' >= n - off) m' in
        if n == offLen then return (PS fp 0 m)
        else do
            let poke8 k v = poke (ptr `plusPtr` k) (fromIntegral v :: Word8)
                ensure k (act :: Ptr Word8 -> IO ByteString) {-LIQUID CAST-} =
                  --LIQUID GHOST added `ptr` to `ensure` so we can say its length has been extended
                  if size-m >= k then act ptr
                  else {-# SCC "resizeUtf8/ensure" #-} do
                      let newSize = size *2 --LIQUID `shiftL` 1
                      fp' <- mallocByteString newSize
                      withForeignPtr fp' $ \ptr' ->
                        memcpy ptr' ptr (fromIntegral m)
                      --LIQUID FIXME: figure out how to prove these
                      --types of "restore safety" recursive calls
                      --terminating
                      start newSize n m fp'
                {- INLINE ensure #-}
            case A.unsafeIndexF arr off len n of
             w ->
              if w <= 0x7F  then ensure 1 $ \ptr -> do
                  poke (ptr `plusPtr` m) (fromIntegral w :: Word8)
                  -- A single ASCII octet is likely to start a run of
                  -- them.  We see better performance when we
                  -- special-case this assumption.
                  let end = ptr `plusPtr` size :: Ptr Word8
                      {- LIQUID WITNESS -}
                      ascii (d' :: Int) !t !u =
                        if t == offLen || eqPtr u end {-LIQUID SPECIALIZE u == end || v >= 0x80-} then
                            go d' t (u `minusPtr` ptr)
                        else do
                            let v = A.unsafeIndex arr t
                            if v >= 0x80 then go d' t (u `minusPtr` ptr) else do
                            poke u (fromIntegral v :: Word8)
                            ascii (d'-1) (t+1) (u `plusPtr` 1)
                        --LIQUID LAZY where v = A.unsafeIndex arr t
                  ascii (d-1) (n+1) (ptr `plusPtr` (m+1))
              else if w <= 0x7FF then ensure 2 $ \ptr -> do
                  poke8 m     $ (w `shiftR` 6) + 0xC0
                  poke8 (m+1) $ (w .&. 0x3f) + 0x80
                  go  (offLen-(n+1)) (n+1) (m+2)
              else if 0xD800 <= w && w <= 0xDBFF then ensure 4 $ \ptr -> do
                  let c = ord $ U16.chr2 w (A.unsafeIndex arr (n+1))
                  poke8 m     $ (c `shiftR` 18) + 0xF0
                  poke8 (m+1) $ ((c `shiftR` 12) .&. 0x3F) + 0x80
                  poke8 (m+2) $ ((c `shiftR` 6) .&. 0x3F) + 0x80
                  poke8 (m+3) $ (c .&. 0x3F) + 0x80
                  go (offLen-(n+2)) (n+2) (m+4)
              else ensure 3 $ \ptr -> do
                  poke8 m     $ (w `shiftR` 12) + 0xE0
                  poke8 (m+1) $ ((w `shiftR` 6) .&. 0x3F) + 0x80
                  poke8 (m+2) $ (w .&. 0x3F) + 0x80
                  go (offLen-(n+1)) (n+1) (m+3)


-- | Decode text from little endian UTF-16 encoding.
decodeUtf16LEWith :: E.OnDecodeError -> ByteString -> Text
decodeUtf16LEWith onErr bs = F.unstream (E.streamUtf16LE onErr bs)
{-# INLINE decodeUtf16LEWith #-}

-- | Decode text from little endian UTF-16 encoding.
--
-- If the input contains any invalid little endian UTF-16 data, an
-- exception will be thrown.  For more control over the handling of
-- invalid data, use 'decodeUtf16LEWith'.
decodeUtf16LE :: ByteString -> Text
decodeUtf16LE = decodeUtf16LEWith E.strictDecode
{-# INLINE decodeUtf16LE #-}

-- | Decode text from big endian UTF-16 encoding.
decodeUtf16BEWith :: E.OnDecodeError -> ByteString -> Text
decodeUtf16BEWith onErr bs = F.unstream (E.streamUtf16BE onErr bs)
{-# INLINE decodeUtf16BEWith #-}

-- | Decode text from big endian UTF-16 encoding.
--
-- If the input contains any invalid big endian UTF-16 data, an
-- exception will be thrown.  For more control over the handling of
-- invalid data, use 'decodeUtf16BEWith'.
decodeUtf16BE :: ByteString -> Text
decodeUtf16BE = decodeUtf16BEWith E.strictDecode
{-# INLINE decodeUtf16BE #-}

-- | Encode text using little endian UTF-16 encoding.
encodeUtf16LE :: Text -> ByteString
encodeUtf16LE txt = E.unstream (E.restreamUtf16LE (F.stream txt))
{-# INLINE encodeUtf16LE #-}

-- | Encode text using big endian UTF-16 encoding.
encodeUtf16BE :: Text -> ByteString
encodeUtf16BE txt = E.unstream (E.restreamUtf16BE (F.stream txt))
{-# INLINE encodeUtf16BE #-}

-- | Decode text from little endian UTF-32 encoding.
decodeUtf32LEWith :: E.OnDecodeError -> ByteString -> Text
decodeUtf32LEWith onErr bs = F.unstream (E.streamUtf32LE onErr bs)
{-# INLINE decodeUtf32LEWith #-}

-- | Decode text from little endian UTF-32 encoding.
--
-- If the input contains any invalid little endian UTF-32 data, an
-- exception will be thrown.  For more control over the handling of
-- invalid data, use 'decodeUtf32LEWith'.
decodeUtf32LE :: ByteString -> Text
decodeUtf32LE = decodeUtf32LEWith E.strictDecode
{-# INLINE decodeUtf32LE #-}

-- | Decode text from big endian UTF-32 encoding.
decodeUtf32BEWith :: E.OnDecodeError -> ByteString -> Text
decodeUtf32BEWith onErr bs = F.unstream (E.streamUtf32BE onErr bs)
{-# INLINE decodeUtf32BEWith #-}

-- | Decode text from big endian UTF-32 encoding.
--
-- If the input contains any invalid big endian UTF-32 data, an
-- exception will be thrown.  For more control over the handling of
-- invalid data, use 'decodeUtf32BEWith'.
decodeUtf32BE :: ByteString -> Text
decodeUtf32BE = decodeUtf32BEWith E.strictDecode
{-# INLINE decodeUtf32BE #-}

-- | Encode text using little endian UTF-32 encoding.
encodeUtf32LE :: Text -> ByteString
encodeUtf32LE txt = E.unstream (E.restreamUtf32LE (F.stream txt))
{-# INLINE encodeUtf32LE #-}

-- | Encode text using big endian UTF-32 encoding.
encodeUtf32BE :: Text -> ByteString
encodeUtf32BE txt = E.unstream (E.restreamUtf32BE (F.stream txt))
{-# INLINE encodeUtf32BE #-}

foreign import ccall unsafe "_hs_text_decode_utf8" c_decode_utf8'
    :: MutableByteArray# s -> Ptr CSize
    -> Ptr Word8 -> Ptr Word8 -> IO (Ptr Word8)
c_decode_utf8 :: A.MArray s -> Ptr CSize -> Ptr Word8 -> Ptr Word8 -> IO (Ptr Word8)
c_decode_utf8 ma = c_decode_utf8' (A.maBA ma)
{-@ assume
    c_decode_utf8 :: a:A.MArray s
                  -> d:{v:PtrV CSize | (BtwnI (deref v) 0 (malen a))}
                  -> c:PtrV Word8
                  -> end:{v:PtrV Word8 | (((plen v) <= (plen c))
                                       && ((pbase v) = (pbase c)))}
                  -> IO {v:(PtrV Word8) | ((BtwnI (plen v) (plen end) (plen c))
                                        && ((pbase v) = (pbase end)))}
  @-}
