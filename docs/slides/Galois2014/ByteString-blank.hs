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

{- measure fplen :: ForeignPtr a -> Int -}

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
        return $ PS fp 2 3























create l f = do
    fp <- mallocForeignPtrBytes l
    withForeignPtr fp $ \p -> f p
    return $! PS fp 0 l


























foo = create 5 $ \p -> poke (p `plusPtr` 4) (0 :: Word8)


































pack str = unsafeCreate (length str) $ \p -> go p  str
  where
    go _ []     = return ()
    go p (x:xs) = poke p x >> go (p `plusPtr` 1) xs

































unsafeIndex (PS x s l) i = liquidAssert (i >= 0 && i < l)  $
    unsafePerformIO $ withForeignPtr x $ \p -> peekByteOff p (s+i)




good = let b = pack [1,2,3]
       in unsafeIndex b 2






















-----------------------------------------------------------------------
-- Helper Code
-----------------------------------------------------------------------
{-@ unsafeCreate :: l:Nat -> (PtrN Word8 l -> IO ()) -> (ByteStringN l) @-}
unsafeCreate n f = unsafePerformIO $ create n f

{-@ invariant {v:ByteString   | bLength  v >= 0} @-}

{-@ qualif PLLen(v:a, p:b) : (len v) <= (plen p) @-}
{-@ qualif ForeignPtrN(v:ForeignPtr a, n:int): fplen v = n @-}
{-@ qualif FPLenPLen(v:Ptr a, fp:ForeignPtr a): fplen fp = plen v @-}
{-@ qualif PtrLen(v:Ptr a, xs:List b): plen v = len xs @-}
{-@ qualif PlenEq(v: Ptr a, x: int): x <= (plen v) @-}

-- Local Variables:
-- flycheck-checker: haskell-liquid
-- End:

create :: Int -> (Ptr Word8 -> IO ()) -> IO ByteString
unsafeIndex :: ByteString -> Int -> Word8

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diffcheck"      @-}
{-@ LIQUID "--short-names"    @-}
