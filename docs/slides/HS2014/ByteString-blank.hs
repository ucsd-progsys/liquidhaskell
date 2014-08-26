{-@ LIQUID "--no-termination" @-}
{- LIQUID "--diffcheck"      @-}
{-@ LIQUID "--short-names"    @-}
{-# LANGUAGE ForeignFunctionInterface #-}
module Bytestring where

import Prelude hiding (null)
import Data.Char
import Data.Word
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr
import Foreign.Storable
import System.IO.Unsafe
import Language.Haskell.Liquid.Prelude


data ByteString = PS { bPayload :: ForeignPtr Word8
                     , bOffset  :: !Int
                     , bLength  :: !Int
                     }


{-@ data ByteString = PS
      { bPayload :: ForeignPtr Word8
      , bOffset  :: {v:Nat | v           <= fplen bPayload}
      , bLength  :: {v:Nat | bOffset + v <= fplen bPayload}
      }
  @-}

{-@ type ByteStringN N = {v:ByteString | bLength v = N} @-}
























{-@ type ForeignN a N = {v:ForeignPtr a | fplen v = N} @-}
{-@ assume mallocForeignPtrBytes :: n:Nat -> IO (ForeignN a n) @-}




bs = do fp <- mallocForeignPtrBytes 5
        return $ PS fp 0 5






























create :: Int -> (Ptr Word8 -> IO ()) -> IO ByteString
create l f = do
    fp <- mallocForeignPtrBytes l
    withForeignPtr fp $ \p -> f p
    return $! PS fp 0 l


bad_create = create 5 $ \p -> poke (p `plusPtr` 10) (0 :: Word8)

{- measure plen :: Ptr a -> Int -}

{-@ assume plusPtr :: p:Ptr a -> n:Int -> Ptr b @-}
{-@ assume poke :: Storable a => Ptr a -> a -> IO () @-}




























-- pack str = unsafeCreate (length str) $ \p -> go p str
--   where
--     go _ []     = return ()
--     go p (x:xs) = poke p x >> go (p `plusPtr` 1) xs








-- unsafeIndex :: ByteString -> Int -> Word8
-- unsafeIndex (PS x s l) i = liquidAssert (i >= 0 && i < l) $
--     unsafePerformIO $ withForeignPtr x $ \p -> peekByteOff p (s+i)



-- good = let b = pack [1,2,3]
--        in unsafeIndex b 2























-----------------------------------------------------------------------
-- Helper Code
-----------------------------------------------------------------------
{-@ unsafeCreate :: l:Nat -> ((PtrN Word8 l) -> IO ()) -> (ByteStringN l) @-}
unsafeCreate n f = unsafePerformIO $ create n f

{-@ invariant {v:ByteString   | bLength  v >= 0} @-}

{-@ qualif PLLen(v:a, p:b) : (len v) <= (plen p) @-}
{-@ qualif ForeignPtrN(v:ForeignPtr a, n:int): fplen v = n @-}
{-@ qualif FPLenPLen(v:Ptr a, fp:ForeignPtr a): fplen fp = plen v @-}
{-@ qualif PtrLen(v:Ptr a, xs:List b): plen v = len xs @-}
{-@ qualif PlenEq(v: Ptr a, x: int): x <= (plen v) @-}

{-@ unsafeHead :: {v:ByteString | (bLength v) > 0} -> Word8 @-}
unsafeHead :: ByteString -> Word8
unsafeHead (PS x s l) = liquidAssert (l > 0) $
  unsafePerformIO  $  withForeignPtr x $ \p -> peekByteOff p s

{-@ unsafeTail :: b:{v:ByteString | (bLength v) > 0}
               -> {v:ByteString | (bLength v) = (bLength b) - 1} @-}
unsafeTail :: ByteString -> ByteString
unsafeTail (PS ps s l) = liquidAssert (l > 0) $ PS ps (s+1) (l-1)

{-@ null :: b:ByteString -> {v:Bool | ((Prop v) <=> ((bLength b) = 0))} @-}
null :: ByteString -> Bool
null (PS _ _ l) = liquidAssert (l >= 0) $ l <= 0

{-@ unsafeTake :: n:Nat -> b:{v: ByteString | n <= (bLength v)} -> (ByteStringN n) @-}
unsafeTake :: Int -> ByteString -> ByteString
unsafeTake n (PS x s l) = liquidAssert (0 <= n && n <= l) $ PS x s n

{-@ unsafeDrop :: n:Nat
               -> b:{v: ByteString | n <= (bLength v)} 
               -> {v:ByteString | (bLength v) = (bLength b) - n} @-}
unsafeDrop  :: Int -> ByteString -> ByteString
unsafeDrop n (PS x s l) = liquidAssert (0 <= n && n <= l) $ PS x (s+n) (l-n)

{-@ cons :: Word8 -> b:ByteString -> {v:ByteString | (bLength v) = 1 + (bLength b)} @-}
cons :: Word8 -> ByteString -> ByteString
cons c (PS x s l) = unsafeCreate (l+1) $ \p -> withForeignPtr x $ \f -> do
        poke p c
        memcpy (p `plusPtr` 1) (f `plusPtr` s) (fromIntegral l)

{-@ empty :: {v:ByteString | (bLength v) = 0} @-} 
empty :: ByteString
empty = PS nullForeignPtr 0 0

{-@ assume
    c_memcpy :: dst:(PtrV Word8)
             -> src:(PtrV Word8) 
             -> size: {v:CSize | (v <= (plen src) && v <= (plen dst))} 
             -> IO (Ptr Word8)
  @-}
foreign import ccall unsafe "string.h memcpy" c_memcpy
    :: Ptr Word8 -> Ptr Word8 -> CSize -> IO (Ptr Word8)

{-@ memcpy :: dst:(PtrV Word8)
           -> src:(PtrV Word8) 
           -> size: {v:CSize | (v <= (plen src) && v <= (plen dst))} 
           -> IO () 
  @-}
memcpy :: Ptr Word8 -> Ptr Word8 -> CSize -> IO ()
memcpy p q s = c_memcpy p q s >> return ()

{-@ assume nullForeignPtr :: {v: ForeignPtr Word8 | (fplen v) = 0} @-}
nullForeignPtr :: ForeignPtr Word8
nullForeignPtr = unsafePerformIO $ newForeignPtr_ nullPtr
{-# NOINLINE nullForeignPtr #-}

-- Local Variables:
-- flycheck-checker: haskell-liquid
-- End:
