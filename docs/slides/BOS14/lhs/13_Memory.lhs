Low Level Memory Manipulation
=============================

 {#mem}
-------

<div class="hidden">

\begin{code}
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
import Language.Haskell.Liquid.Prelude
\end{code}

</div>

"HeartBleed" in Haskell
-----------------------

<br>

**Modern languages are built on top of C**

<br>

<div class="fragment">
Implementation errors could open up vulnerabilities
</div>




"HeartBleed" in Haskell (1/3)
-----------------------------

**A String Truncation Function**

<br>

<div class="hidden">
\begin{spec}
import Data.ByteString.Char8  (pack, unpack) 
import Data.ByteString.Unsafe (unsafeTake)
\end{spec}
</div>

\begin{spec}
chop     :: String -> Int -> String
chop s n = s'
  where 
    b    = pack s           -- down to low-level
    b'   = unsafeTake n b   -- grab n chars
    s'   = unpack b'        -- up to high-level
\end{spec}

"HeartBleed" in Haskell (2/3)
-----------------------------

<img src="../img/overflow.png" height=100px>


Works if you use the **valid prefix** size 

<br>

\begin{spec}
λ> let ex = "Ranjit Loves Burritos"

λ> heartBleed ex 10
"Ranjit Lov"
\end{spec}


"HeartBleed" in Haskell (3/3)
-----------------------------

<img src="../img/overflow.png" height=100px>

Leaks *overflow buffer* if **invalid prefix** size!

<br>

\begin{spec}
λ> let ex = "Ranjit Loves Burritos"

λ> heartBleed ex 30
"Ranjit Loves Burritos\NUL\201\&1j\DC3\SOH\NUL"
\end{spec}

Types Against Overflows
-----------------------

<br>

**Strategy: Specify and Verify Types for**

<br>

1. <div class="fragment">Low-level `Pointer` API</div>
2. <div class="fragment">Lib-level `ByteString` API</div>
3. <div class="fragment">User-level `Application` API</div>

<br>

<div class="fragment">Errors at *each* level are prevented by types at *lower* levels</div>

 {#ptr}
=======

1. Low-level Pointer API 
------------------------

<br>

Strategy: Specify and Verify Types for

<br>

1. **Low-level `Pointer` API**
2. Lib-level `ByteString` API
3. User-level `Application` API

<br>

Errors at *each* level are prevented by types at *lower* levels




1. Low-Level Pointer API
========================

API: Types 
----------

<br>

**Low-level Pointers**

\begin{spec}
data Ptr a         
\end{spec}

<br>

<div class="fragment">
**Foreign Pointers**

\begin{spec}
data ForeignPtr a 
\end{spec}

<br>

`ForeignPtr` wraps around `Ptr`; can be exported to/from C.
</div>


API: Operations (1/2)
---------------------

<div class="fragment">
**Read** 

\begin{spec}
peek     :: Ptr a -> IO a  
\end{spec}
</div>

<br>
<div class="fragment">
**Write** 

\begin{spec}
poke     :: Ptr a -> a -> IO ()
\end{spec}
</div>

<br>

<div class="fragment">
**Arithmetic**
\begin{spec}
plusPtr  :: Ptr a -> Int -> Ptr b 
\end{spec}
</div>

API: Operations (2/2)
---------------------

<div class="fragment">
**Create**

\begin{spec}
malloc  :: Int -> ForeignPtr a
\end{spec}
</div>

<br>

<div class="fragment">
**Unwrap and Use**

\begin{spec}
withForeignPtr :: ForeignPtr a     -- pointer 
               -> (Ptr a -> IO b)  -- action 
               -> IO b             -- result
\end{spec}
</div>

Example
-------

**Allocate a block and write 4 zeros into it**

<div class="fragment">

\begin{code}
zero4 = do fp <- malloc 4
           withForeignPtr fp $ \p -> do
             poke (p `plusPtr` 0) zero 
             poke (p `plusPtr` 1) zero 
             poke (p `plusPtr` 2) zero 
             poke (p `plusPtr` 3) zero 
           return fp
        where
           zero = 0 :: Word8
\end{code}

</div>

Example
-------

**Allocate a block and write 4 zeros into it**

How to *prevent overflows* e.g. writing 5 or 50 zeros?

<br>

<div class="fragment">
**Step 1**

*Refine pointers* with allocated size
</div>

<br>

<div class="fragment">
**Step 2**

*Track sizes* in pointer operations
</div>

Refined API: Types
------------------

<br>

**1. Refine pointers with allocated size**

\begin{spec}
measure plen  :: Ptr a -> Int 
measure fplen :: ForeignPtr a -> Int 
\end{spec}

<br>

<div class="fragment">
Abbreviations for pointers of size `N`

\begin{spec}
type PtrN a N        = {v:_ |  plen v  = N} 
type ForeignPtrN a N = {v:_ |  fplen v = N} 
\end{spec}
</div>


Refined API: Ops (1/3)
----------------------

<div class="fragment">
**Create**

\begin{spec}
malloc  :: n:Nat -> ForeignPtrN a n
\end{spec}
</div>

<br>

<div class="fragment">
**Unwrap and Use**

\begin{spec}
withForeignPtr :: fp:ForeignPtr a 
               -> (PtrN a (fplen fp) -> IO b)  
               -> IO b             
\end{spec}
</div>

Refined API: Ops (2/3)
----------------------

<br>

**Arithmetic**

Refine type to track *remaining* buffer size

<br>

<div class="fragment">
\begin{spec}
plusPtr :: p:Ptr a
        -> o:{Nat|o <= plen p}   -- in bounds
        -> PtrN b (plen b - o)   -- remainder
\end{spec}

</div>



Refined API: Ops (3/3)
----------------------

**Read & Write require non-empty remaining buffer**

<br>

<div class="fragment">
**Read** 

\begin{spec}
peek :: {v:Ptr a | 0 < plen v} -> IO a  
\end{spec}
</div>

<br>
<div class="fragment">
**Write** 

\begin{spec}
poke :: {v:Ptr a | 0 < plen v} -> a -> IO ()  
\end{spec}
</div>

Example: Overflow Prevented
---------------------------

How to *prevent overflows* e.g. writing 5 or 50 zeros?

<br>

<div class="fragment">

\begin{code}
exBad = do fp <- malloc 4
           withForeignPtr fp $ \p -> do
             poke (p `plusPtr` 0) zero 
             poke (p `plusPtr` 1) zero 
             poke (p `plusPtr` 2) zero 
             poke (p `plusPtr` 5) zero 
           return fp
        where
           zero = 0 :: Word8
\end{code}

</div>

 {#bs}
======

2. ByteString API
-----------------

<br>

Strategy: Specify and Verify Types for

<br>

1. Low-level `Pointer` API
2. **Lib-level `ByteString` API**
3. User-level `Application` API

<br>

Errors at *each* level are prevented by types at *lower* levels


2. ByteString API
=================

Type
-------

<img src="../img/bytestring.png" height=150px>

\begin{code}
data ByteString = PS {
    bPtr    :: ForeignPtr Word8
  , bOff    :: !Int
  , bLen :: !Int
  }
\end{code}


Refined Type 
------------

<img src="../img/bytestring.png" height=150px>

\begin{code}
{-@ data ByteString = PS {
      bPtr    :: ForeignPtr Word8
    , bOff    :: {v:Nat|v  <= fplen bPtr}
    , bLen :: {v:Nat|v + bOff <= fplen bPtr}
    }                                       @-}
\end{code}

<div class="fragment">
**A Useful Abbreviation**

\begin{spec}
type ByteStringN N = {v:ByteString | bLen v = N} 
\end{spec}

<div class="hidden">
\begin{code}
{-@ type ByteStringN N = {v:ByteString | bLen v = N} @-}
\end{code}
</div>
</div>



Legal Bytestrings 
-----------------


<br>

\begin{code}
{-@ good1 :: IO (ByteStringN 5) @-}
good1 = do fp <- malloc 5
           return $ PS fp 0 5

{-@ good1 :: IO (ByteStringN 3) @-}
good2 = do fp <- malloc 5
           return $ PS fp 2 3
\end{code}

<br>

**Note:** *length* of `good2` is `3` which is *less than* allocated size `5`


Illegal Bytestrings 
-----------------

<br>

\begin{code}
bad1 = do fp <- malloc 3 
          return $ PS fp 0 10 

bad2 = do fp <- malloc 3
          return $ PS fp 2 2
\end{code}

<br>

<div class="fragment">
Claimed length *exceeds* allocation ... **rejected** at compile time
</div>

Creating a BS
-------------

Pack To BS
------------

\begin{code}
{-@ pack  :: str:_ -> ByteStringN (len str) @-}
pack str  = create' (length str) $ \p -> go p str
  where
    go _ []     = return ()
    go p (x:xs) = poke p x >> go (p `plusPtr` 1) xs
\end{code}

Unpack From BS
--------------

\begin{code}
{-@ unpack :: b:ByteString -> {v:_ | len v = bLen b} @-}
unpack :: ByteString -> [Word8]

{-@ qualif Unpack(v:a, acc:b, n:int) : len v = 1 + n + len acc @-}

unpack (PS _  _ 0) = []
unpack (PS ps s l) = unsafePerformIO $ withForeignPtr ps $ \p ->
   go (p `plusPtr` s) (l - 1) []
  where
   go p 0 acc = peek p          >>= \e -> return (e : acc)
   go p n acc = peekByteOff p n >>= \e -> go p (n-1) (e : acc)
\end{code}


Take From BS
------------


 {#heartbleedredux}
==================


3. Application API 
-------------------


<br>

Strategy: Specify and Verify Types for

<br>

1. Low-level `Pointer` API
2. Lib-level `ByteString` API
3. **User-level `Application` API**

<br>

Errors at *each* level are prevented by types at *lower* levels


3. Application API 
==================


Compiler rejects `chop`
-----------------------

chopBAD

A Well Typed `chop`
-------------------

chopGOOD

"HeartBleed" no more
--------------------

\begin{code}
demo     = [ex6, ex30]
  where
    ex   = "Ranjit Loves Burritos"
    
    ex6  = chop ex 6

    ex30 = chop ex 30

chop = undefined
\end{code}

"Bleeding" `chop` rejected by compiler.


Recap: Types vs Overflows
-------------------------

<br>

**Strategy: Specify and Verify Types for**

<br>

1. Low-level `Pointer` API
2. Lib-level `ByteString` API
3. User-level `Application` API

<br>

Errors at *each* level are prevented by types at *lower* levels


END HERE







\begin{spec}
{-@ measure fplen :: ForeignPtr a -> Int @-}
\end{spec}

and use it to define a foreign-pointer to a segment containing *N* bytes

Since we haven't defined any equations for `fplen` we won't get strengthed 
constructors. Instead, we will *assume* that `malloc` behaves sensibly and
allocates the number of bytes you asked for.
 
The crucial invariant is that we should only be able to reach valid memory 
locations via the offset and length, i.e. the sum `off + len` *must not exceed* 
the "length" of the pointer.


LiquidHaskell won't let us build a `ByteString` that claims to have more valid 
indices than it *actually* does

even if we try to be sneaky with the length parameter.


Creating ByteStrings
--------------------

\begin{code}
{-@ create' :: n:Nat -> (PtrN Word8 n -> IO ()) -> ByteStringN n @-}
create'  :: Int -> (Ptr Word8 -> IO ()) -> ByteString
create' n f = unsafePerformIO $ do
    fp <- mallocForeignPtrBytes n
    withForeignPtr fp $ \p -> f p
    return $! PS fp 0 n
\end{code}

But this seems horribly unsafe!

What's to stop the parameter `f` from poking any random,
invalid offset from the pointer it wants to?

We could, e.g.

* create a BS of size `5`, and
* write a `0` at the index `10`.

ASIDE: have these assumed types around to suppress the type-errors that LH will 
       show, just remove them when script introduces type

{- assume plusPtr :: p:Ptr a -> n:Int -> Ptr b      @-}
{- assume poke :: Storable a => Ptr a -> a -> IO () @-}

END ASIDE

\begin{code}
bad_create = create' 5 $ \p -> poke (p `plusPtr` 10) (0 :: Word8)
\end{code}

\begin{code}
good_create = create' 5 $ \p -> poke (p `plusPtr` 2) (0 :: Word8)
\end{code}


ES: CUT


Nested Data
-----------

For a more in depth example, let's take a look at `group`,
which transforms strings like

   `"foobaaar"`

into *lists* of strings like

   `["f","oo", "b", "aaa", "r"]`.

The specification is that `group` should produce a list of `ByteStrings`

1. that are all *non-empty* (safety)
2. the sum of whose lengths is equal to the length of the input string (precision)

We use the type alias

\begin{code}
{-@ type ByteStringNE = {v:ByteString | bLen v > 0} @-}
\end{code}

to specify (safety) and introduce a new measure

\begin{code}
{-@ measure bLens  :: [ByteString] -> Int
    bLens ([])   = 0
    bLens (x:xs) = (bLen x + bLens xs)
  @-}
\end{code}

to specify (precision). The full type-specification looks like this:

\begin{code}
{-@ group :: b:ByteString -> {v: [ByteStringNE] | bLens v = bLen b} @-}
group xs
    | null xs   = []
    | otherwise = let y = unsafeHead xs
                      (ys, zs) = spanByte (unsafeHead xs) (unsafeTail xs)
                  in (y `cons` ys) : group zs
\end{code}

As you can probably tell, `spanByte` appears to be doing a lot of the work here,
so let's take a closer look at it to see why the post-condition holds.

\begin{code}
spanByte :: Word8 -> ByteString -> (ByteString, ByteString)
spanByte c ps@(PS x s l) = unsafePerformIO $ withForeignPtr x $ \p ->
    go (p `plusPtr` s) 0
  where
    go p i | i >= l    = return (ps, empty)
           | otherwise = do c' <- peekByteOff p i
                            if c /= c'
                                then return (unsafeTake i ps, unsafeDrop i ps)
                                else go p (i+1)
\end{code}

LiquidHaskell infers that `0 <= i <= l` and therefore that all of the memory
accesses are safe. Furthermore, due to the precise specifications given to
`unsafeTake` and `unsafeDrop`, it is able to prove that `spanByte` has the type

\begin{code}
{-@ spanByte :: Word8 -> b:ByteString -> (ByteStringPair b) @-}
\end{code}

where `ByteStringPair b` describes a pair of `ByteString`s whose lengths sum to
the length of `b`.

\begin{code}
{-@ type ByteStringPair B = (ByteString, ByteString)<{\x1 x2 ->
       bLen x1 + bLen x2 = bLen B}> @-}
\end{code}


\begin{code}
-----------------------------------------------------------------------
-- Helper Code
-----------------------------------------------------------------------
{-@ unsafeCreate :: l:Nat -> ((PtrN Word8 l) -> IO ()) -> (ByteStringN l) @-}
unsafeCreate n f = create' n f -- unsafePerformIO $ create n f

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

{-@ unsafeTake :: n:Nat -> b:{v: ByteString | n <= (bLen v)} -> (ByteStringN n) @-}
unsafeTake :: Int -> ByteString -> ByteString
unsafeTake n (PS x s l) = liquidAssert (0 <= n && n <= l) $ PS x s n

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

{-@ assume mallocForeignPtrBytes :: n:Nat -> IO (ForeignPtrN a n) @-}
{-@ type ForeignPtrN a N = {v:ForeignPtr a | fplen v = N} @-}
{-@ malloc :: n:Nat -> IO (ForeignPtrN a n) @-}
malloc = mallocForeignPtrBytes 

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
\end{code}
