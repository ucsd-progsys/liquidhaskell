{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--diffcheck"     @-}
{-# LANGUAGE ForeignFunctionInterface #-}

module Memory where

import Prelude hiding (null)
import Data.Char
import Data.Word
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr
import Foreign.Storable
import System.IO.Unsafe
import Data.ByteString.Internal (c2w, w2c)
import Language.Haskell.Liquid.Prelude


-- | Memory API

-- data Ptr a
-- data ForeignPtr a

{-@ type OkPtr a = {v:Ptr a | 0 < plen v} @-}

-- | Malloc

{-@ assume mallocForeignPtrBytes :: n:Nat -> IO (ForeignPtrN a n) @-}
{-@ malloc :: n:Nat -> IO (ForeignPtrN a n) @-}
malloc = mallocForeignPtrBytes 

-- withForeignPtr :: fp:ForeignPtr a -> (PtrN a (fplen fp) -> IO b) -> IO b             
-- plusPtr :: p:Ptr a -> o:{Nat|o <= plen p} -> PtrN b (plen b - o)
-- peek    :: OkPtr a -> IO a  
-- poke    :: OkPtr a -> a -> IO ()  



zero4 = do fp <- malloc 4
           withForeignPtr fp $ \p -> do
             poke (p `plusPtr` 0) zero 
             poke (p `plusPtr` 1) zero 
             poke (p `plusPtr` 2) zero 
             poke (p `plusPtr` 3) zero 
           return fp
        where
           zero = 0 :: Word8


-- | How to prevent **overflows** e.g. writing 5 or 50 zeros?

zero4' = do fp <- malloc 4
            withForeignPtr fp $ \p -> do
              poke (p `plusPtr` 0) zero 
              poke (p `plusPtr` 1) zero 
              poke (p `plusPtr` 2) zero 
              poke (p `plusPtr` 5) zero 
            return fp
        where
           zero = 0 :: Word8
