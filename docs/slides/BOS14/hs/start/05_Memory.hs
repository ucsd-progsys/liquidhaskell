{-# LANGUAGE ForeignFunctionInterface #-}

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--diffcheck"     @-}

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


------------------------------------------------------------------------
-- | 1. Low-level Pointer API  -----------------------------------------
------------------------------------------------------------------------

-- | Create a buffer of size 4 and initialize it with zeros

zero4  = do fp <- mallocForeignPtrBytes 4
            withForeignPtr fp $ \p -> do
              poke (p `plusPtr` 0) zero 
              poke (p `plusPtr` 1) zero 
              poke (p `plusPtr` 2) zero 
              poke (p `plusPtr` 3) zero 
            return fp
        where
            zero = 0 :: Word8

-- But whats to prevent an overflow, e.g. writing to offset 5 or 50?
            


-- | Types for Pointers

-- data Ptr a         
-- data ForeignPtr a 

-- | Size of Ptr and ForeignPtr

-- measure plen  :: Ptr a -> Int 
-- measure fplen :: ForeignPtr a -> Int 


{-@ type PtrN a N        = {v:Ptr a        |  plen v  = N}  @-}
{-@ type ForeignPtrN a N = {v:ForeignPtr a |  fplen v = N}  @-}

-- | Allocating Memory

{-@ assume mallocForeignPtrBytes :: n:Nat -> IO (ForeignPtrN a n) @-}

-- | Using a pointer

{- withForeignPtr :: fp:ForeignPtr a 
                  -> (PtrN a (fplen fp) -> IO b)  
                  -> IO b             
-}

-- | Pointer Arithmetic

{- plusPtr :: p:Ptr a
           -> o:{Nat|o <= plen p}   -- in bounds
           -> PtrN b (plen b - o)   -- remainder
-}

-- | Read and Write

{- peek :: {v:Ptr a | 0 < plen v} -> IO a  
   poke :: {v:Ptr a | 0 < plen v} -> a -> IO ()  
 -}

-- | Example: Preventing Overflows e.g. writing 5 or 50 zeros?

zero4' = do fp <- mallocForeignPtrBytes 4
            withForeignPtr fp $ \p -> do
              poke (p `plusPtr` 0) zero 
              poke (p `plusPtr` 1) zero 
              poke (p `plusPtr` 2) zero 
              poke (p `plusPtr` 5) zero 
            return fp
        where
            zero = 0 :: Word8



------------------------------------------------------------------------
-- | 2. ByteString API -------------------------------------------------
------------------------------------------------------------------------

data ByteString = PS {
    bPtr :: ForeignPtr Word8
  , bOff :: !Int
  , bLen :: !Int
  }


-- | Refined Type, with invariants

{-@ data ByteString = PS {
      bPtr :: ForeignPtr Word8
    , bOff :: {v:Nat| v        <= fplen bPtr}
    , bLen :: {v:Nat| v + bOff <= fplen bPtr}
    }

  @-}

-- | Some useful abbreviations

{-@ type ByteStringN N = {v:ByteString | bLen v = N} @-}
{-@ type StringN N     = {v:String     | len v  = N} @-}

-- | Legal Bytestrings 

{-@ good1 :: IO (ByteStringN 5) @-}
good1 = do fp <- mallocForeignPtrBytes 5
           return $ PS fp 0 5

{-@ good2 :: IO (ByteStringN 3) @-}
good2 = do fp <- mallocForeignPtrBytes 5
           return $ PS fp 2 3

-- | Illegal Bytestrings 

bad1 = do fp <- mallocForeignPtrBytes 3 
          return $ PS fp 0 10 

bad2 = do fp <- mallocForeignPtrBytes 3
          return $ PS fp 2 2



-- | ByteString API: `create`

create :: Int -> (Ptr Word8 -> IO ()) -> ByteString

create n fill = unsafePerformIO $ do
  fp  <- mallocForeignPtrBytes n
  withForeignPtr fp fill 
  return $! PS fp 0 n


-- Yikes, there is an error! How to fix?

-- | ByteStringN API: `unsafeTake`

unsafeTake n (PS x s l) = PS x s n

-- Wow, thats super fast. O(1)! But how to fix the error?

-- | ByteString API: `pack`

pack          :: String -> ByteString
pack str      = create n $ \p -> go p xs
  where
  n           = length str
  xs          = map c2w str
  go p (x:xs) = poke p x >> go (plusPtr p 1) xs
  go _ []     = return  ()

-- Hmm. How to fix the error?



-- | ByteString API: `unpack` 



{-@ qualif Unpack(v:a, acc:b, n:int) : len v = 1 + n + len acc @-}

unpack :: ByteString -> String 
unpack (PS _  _ 0)  = []
unpack (PS ps s l)  = unsafePerformIO $ withForeignPtr ps $ \p ->
   go (p `plusPtr` s) (l - 1)  []
  where
   go p 0 acc = peek p >>= \e -> return (w2c e : acc)
   go p n acc = peek (p `plusPtr` n) >>= \e -> go p (n-1) (w2c e : acc)



------------------------------------------------------------------------
-- | 3. Application API (Heartbleed no more!) --------------------------
------------------------------------------------------------------------

chop     :: String -> Int -> String 
chop s n =  s'
  where 
    b    = pack s          -- down to low-level
    b'   = unsafeTake n b  -- grab n chars
    s'   = unpack b'       -- up to high-level

-- Whats the problem?





-- | "HeartBleed" no more

demo     = [ex6, ex30]
  where
    ex   = ['R','a','n','j','i','t']
    ex6  = chop ex 6  -- ok
    ex30 = chop ex 30 -- out of bounds


-- "Bleeding" `chop ex 30` *rejected* by compiler



------------------------------------------------------------------------
-- | 3. Bonus Material -------------------------------------------------
------------------------------------------------------------------------

-- | `group` ing ByteStrings 

{- How shall we type `group` where

     group "foobaaar"

   returns

     ["f","oo", "b", "aaa", "r"]

-}

-- | An alias for NON-EMPTY ByteStrings
    
{-@ type ByteStringNE = {v:ByteString | bLen v > 0} @-}

-- | A measure for the sum of sizes of a LIST of ByteStrings
    
{-@ measure bLens  :: [ByteString] -> Int
    bLens ([])   = 0
    bLens (x:xs) = (bLen x + bLens xs)
  @-}

-- | @group@
    
{-@ group :: b:ByteString -> {v: [ByteStringNE] | bLens v = bLen b} @-}
group xs
    | null xs   = []
    | otherwise = let y = unsafeHead xs
                      (ys, zs) = spanByte (unsafeHead xs) (unsafeTail xs)
                  in (y `cons` ys) : group zs


-- | @spanByte@ does the heavy lifting

{-@ spanByte :: Word8 -> b:ByteString -> (ByteStringPair b) @-}
spanByte :: Word8 -> ByteString -> (ByteString, ByteString)
spanByte c ps@(PS x s l) = unsafePerformIO $ withForeignPtr x $ \p ->
    go (p `plusPtr` s) 0
  where
    go p i | i >= l    = return (ps, empty)
           | otherwise = do c' <- peekByteOff p i
                            if c /= c'
                                then return (unsafeTake i ps, unsafeDrop i ps)
                                else go p (i+1)

-- | Using the alias
                            
{-@ type ByteStringPair B = (ByteString, ByteString)<{\x1 x2 ->
       bLen x1 + bLen x2 = bLen B}> @-}











----------------------------------------------------------------------------
-- | CHEAT AREA
----------------------------------------------------------------------------

-- #START ERRORS 13
-- #END   ERRORS 4 (zero4', bad1, bad2, ex30) 
                            
{- create     :: n:Nat -> (PtrN Word8 n -> IO ()) -> ByteStringN n      @-}
{- unsafeTake :: n:Nat -> b:{ByteString | n <= bLen b} -> ByteStringN n @-}
{- pack       :: s:String -> ByteStringN (len s)                        @-}
{- unpack     :: b:ByteString -> {v:String | len v = bLen b}            @-}
{- chop       :: s:String -> n:{Nat | n <= len s} -> StringN n          @-} 



























-----------------------------------------------------------------------
-- | Helper Code (Stuff from BS benchmark, to make demo self-contained)
-----------------------------------------------------------------------

{-@ unsafeCreate :: l:Nat -> ((PtrN Word8 l) -> IO ()) -> (ByteStringN l) @-}
unsafeCreate n f = create n f -- unsafePerformIO $ create n f

{-@ invariant {v:ByteString   | bLen  v >= 0} @-}
{-@ invariant {v:[ByteString] | bLens v >= 0} @-}

{-@ qualif PLLen(v:a, p:b) : (len v) <= (plen p) @-}
{-@ qualif ForeignPtrN(v:ForeignPtr a, n:int): fplen v = n @-}
{-@ qualif FPLenPLen(v:Ptr a, fp:ForeignPtr a): fplen fp = plen v @-}
{-@ qualif PtrLen(v:Ptr a, xs:List b): plen v = len xs @-}
{-@ qualif PlenEq(v: Ptr a, x: int): x <= (plen v) @-}

{-@ unsafeHead :: {v:ByteString | (bLen v) > 0} -> Word8 @-}

unsafeHead :: ByteString -> Word8
unsafeHead (PS x s l) = liquidAssert (l > 0) $
  unsafePerformIO  $  withForeignPtr x $ \p -> peekByteOff p s

{-@ unsafeTail :: b:{v:ByteString | (bLen v) > 0}
               -> {v:ByteString | (bLen v) = (bLen b) - 1} @-}
unsafeTail :: ByteString -> ByteString
unsafeTail (PS ps s l) = liquidAssert (l > 0) $ PS ps (s+1) (l-1)

{-@ null :: b:ByteString -> {v:Bool | ((Prop v) <=> ((bLen b) = 0))} @-}
null :: ByteString -> Bool
null (PS _ _ l) = liquidAssert (l >= 0) $ l <= 0

{-@ unsafeDrop :: n:Nat
               -> b:{v: ByteString | n <= (bLen v)} 
               -> {v:ByteString | (bLen v) = (bLen b) - n} @-}
unsafeDrop  :: Int -> ByteString -> ByteString
unsafeDrop n (PS x s l) = liquidAssert (0 <= n && n <= l) $ PS x (s+n) (l-n)

{-@ cons :: Word8 -> b:ByteString -> {v:ByteString | (bLen v) = 1 + (bLen b)} @-}
cons :: Word8 -> ByteString -> ByteString
cons c (PS x s l) = unsafeCreate (l+1) $ \p -> withForeignPtr x $ \f -> do
        poke p c
        memcpy (p `plusPtr` 1) (f `plusPtr` s) (fromIntegral l)

{-@ empty :: {v:ByteString | (bLen v) = 0} @-} 
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



