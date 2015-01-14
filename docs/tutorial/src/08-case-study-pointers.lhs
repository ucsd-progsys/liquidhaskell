Case Study: Pointers Without Overflows
======================================

\begin{comment}

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
import Data.ByteString.Internal (c2w, w2c)
import Language.Haskell.Liquid.Prelude
\end{code}
\end{comment}

A large part of the allure of Haskell is its elegant, high-level ADTs
that ensure that programs won't be plagued by problems like the infamous
[SSL heartbleed bug](heartbleed).
\footnotetext{Assuming, of course, the absence of errors in the compiler and run-time...}
However, another part of Haskell's charm is that when you really really 
need to, you can drop down to low-level pointer twiddling to squeeze the 
most performance out of your machine. But of course, that opens the door 
to the heartbleeds.

Wouldn't it be nice to have have our cake and eat it too? That is wouldn't
it be great if we could twiddle pointers at a low-level and still get the
nice safety assurances of high-level types? In this case study, lets see
how LiquidHaskell lets us do exactly that.


HeartBleeds in Haskell
----------------------

\newthought{Modern Languages} like Haskell are ultimately built upon the
foundation of `C`. Thus, implementation errors could open up unpleasant
vulnerabilities that could easily slither past the type system and even
code inspection.


\newthought{Truncating Strings} As a concrete example, lets look at a
a function that uses the `ByteString` library to truncate strings:

\begin{spec}
chop     :: String -> Int -> String
chop s n = s'
  where 
    b    = B.pack s          -- down to low-level
    b'   = B.unsafeTake n b  -- grab n chars
    s'   = B.unpack b'       -- up to high-level
\end{spec}

\noindent First, the function `pack`s the string into a low-level
bytestring `b`, then it grabs the first `n` `Char`acters from `b`
and translates them back into a high-level `String`. Lets see how
the function works on a small test:

\begin{spec}
ghci> let ex = "Ranjit Loves Burritos"
\end{spec}

\noindent We get the right result when we `chop` a *valid* prefix:

\begin{spec}
ghci> chop ex 10
"Ranjit Lov"
\end{spec}

\noindent But, as illustrated in Figure~\ref{fig:overflow}, the
machine silently reveals (or more colorfully, *bleeds*) the contents
of adjacent memory or if we use an *invalid* prefix:

\begin{spec}
ghci> heartBleed ex 30
"Ranjit Loves Burritos\NUL\201\&1j\DC3\SOH\NUL"
\end{spec}


\begin{figure}[h]
\includegraphics[height=1.0in]{img/overflow.png}
\caption{Can we prevent the program from leaking `secret`s?} 
\label{fig:overflow}
\end{figure}


\newthought{Types against Overflows} Now that we have stared the problem
straight in the eye, look at how we can use LiquidHaskell to *prevent* the
above at compile time. To this end, we decompose the overall system into
a hierarchy of *levels* (i.e. *modules*). In this case, we have three levels:

1. **Machine** level `Pointers`
2. **Library** level `ByteString`
3. **User**    level `Application`

\noindent Now, our strategy, as before, is to develop an *refined API* for
each level such that errors at *each* level are prevented by using the typed
interfaces for the *lower* levels. Next, lets see how this strategy helps develop
a safe means of manipulating pointers.

Low-level Pointer API 
---------------------

To get started, lets look at the low-level pointer API that is
offered by GHC and the run-time. First, lets just see who the
*dramatis personae* are, and how they might let heartbleeds in.
Then, once we have come to grips with the problem, we will see
how to batten down the hatches with LiquidHaskell.

\newthought{Pointers} are an (abstract) type implemented by GHC.
To quote the documentation, "a value of type `Ptr a represents a
pointer to an object, or an array of objects, which may be marshalled
to or from Haskell values of type `a`.

\begin{spec}
data Ptr a         
\end{spec}

\newthought{Foreign Pointers} are *wrapped* pointers that can be
exported to and from C code via the [Foreign Function Interface](foreignptr).

\begin{spec}
data ForeignPtr a 
\end{spec}

\newthought{To Create} a pointer we use `mallocForeignPtrBytes n`
which creates a `Ptr` to a buffer of size `n`, wraps it as a
`ForeignPtr` and returns the result:

\begin{spec}
malloc :: Int -> ForeignPtr a
\end{spec}

\newthought{To Unwrap} and actually use the `ForeignPtr` we use 

\begin{spec}
withForeignPtr :: ForeignPtr a     -- ^ pointer 
               -> (Ptr a -> IO b)  -- ^ action 
               -> IO b             -- ^ result
\end{spec}

\noindent That is, `withForeignPtr fp act` lets us execute a
action `act` on the actual `Ptr` wrapped within the `fp`.
These actions are typically sequences of *dereferences*,
i.e. reads or writes.

\newthought{To Derereference} a pointer, e.g. to read or update
the contents at the corresponding memory location, we use
the functions `peek` and `poke` respectively.
\footnoteteext{We elide the `Storable` type class constraint to
strip the presentation down to the absolute essentials.}

\begin{spec}
-- | Read 
peek :: Ptr a -> IO a           

-- | Write
poke :: Ptr a -> a -> IO ()
\end{spec}

\newthought{For Fine Grained Access} we can directly shift
pointers to arbitrary offsets from the blocks obtained via `malloc`.
This is done via the low-level *pointer arithmetic* operation `plusPtr p off`
which takes a pointer `p` an integer `off` and returns the pointer (address)
obtained shifting `p` by `off`:

\begin{spec}
plusPtr :: Ptr a -> Int -> Ptr b 
\end{spec}

\newthought{Example} That was rather dry; lets look at a concrete
example of how one might use the low-level API. The following
function allocates a block of 4 bytes and fills it with zeros:

\begin{code}
zero4 = do fp <- mallocForeignPtrBytes 4
           withForeignPtr fp $ \p -> do
             poke (p `plusPtr` 0) zero 
             poke (p `plusPtr` 1) zero 
             poke (p `plusPtr` 2) zero 
             poke (p `plusPtr` 3) zero 
           return fp
        where
           zero = 0 :: Word8
\end{code}

\noindent While the above is perfectly all right, a small typo could
easily slip past the type system (and run-time!) leading to hard to find
errors:

\begin{code}
zero4' = do fp <- mallocForeignPtrBytes 4
            withForeignPtr fp $ \p -> do
              poke (p `plusPtr` 0) zero 
              poke (p `plusPtr` 1) zero 
              poke (p `plusPtr` 2) zero 
              poke (p `plusPtr` 8) zero 
            return fp
         where
            zero = 0 :: Word8
\end{code}

A Refined Pointer API
---------------------

Wouldn't it be great if we had an assistant to helpfully point out
the error above as soon as we *wrote* it? To turn LiquidHaskell into
this friend, we will use the following strategy: 

1. **Refine pointers** with allocated buffer size
2. **Track sizes** in pointer operations

\newthought{To Refining Pointers} with the *size* of their associated
buffers, we can use an *abstract measure*, i.e. a measure specification  
*without* any underlying implementation.

\footnotetext{These two measures, and the signatures for
the associate API are defined and imported from in the
LiquidHaskell [standard library](ptrspec). We include them
here for exposition.}

\begin{spec}
-- | Size of `Ptr`
measure plen  :: Ptr a -> Int 

-- | Size of `ForeignPtr`
measure fplen :: ForeignPtr a -> Int 
\end{spec}

\noindent As before, it is helpful to define a few
aliases for pointers of a given size `N`:

\begin{spec}
type PtrN a N        = {v:Ptr a        | plen v  = N} 
type ForeignPtrN a N = {v:ForeignPtr a | fplen v = N} 
\end{spec}

\newthought{Abstract Measures} are extremely useful when we don't have
a concrete implementation of the underlying value, but we know that
the value *exists*.  \footnotetext{This is another example of a
*ghost* specification} Here, we don't have the value -- inside Haskell
-- because the buffers are manipulated within C. However, this is no
cause for alarm as we will simply use measures to refine the API (not
to perform any computations.)

\newthought{To Refine Allocation} we stipulate that
the size parameter be non-negative, and that the returned
pointer indeed refers to a buffer with exactly `n` bytes:

\begin{spec}
mallocForeignPtrBytes :: n:Nat -> ForeignPtrN a n
\end{spec}

\newthought{To Refine Unwrapping} we specify that the *action*
gets as input, an unwrapped `Ptr` whose size *equals* that of the
given `ForeignPtr`.

\begin{spec}
withForeignPtr :: fp:ForeignPtr a 
               -> (PtrN a (fplen fp) -> IO b)  
               -> IO b             
\end{spec}

\noindent This is a rather interesting *higher-order* specification.
Consider a call `withForeignPtr fp act`. If the `act` requires a `Ptr`
whose size *exceeds* that of `fp` then LiquidHaskell will flag a
(subtyping) error indicating the overflow. If instead the `act`
requires a buffer of size less than `fp` then via contra-variant
function subtyping, the input type of `act` will be widened to
the large size, and the code will be accepted.

\newthought{To Refine Reads and Writes} we specify that they can
only be done if the pointer refers to a non-empty (remaining) buffer.
That is, we define an alias:

\begin{spec}
type OkPtr a = {v:Ptr a | 0 < plen v}
\end{spec}

\noindent that describes pointers referring to *non-empty* buffers
(of strictly positive `plen`), and then use the alias to refine:

\begin{spec}
peek :: OkPtr a -> IO a  
poke :: OkPtr a -> a -> IO ()  
\end{spec}

\noindent In essence the above type says that no matter how arithmetic
was used to shift pointers around, when the actual dereference happens,
the size "remaining" after the pointer must be non-negative (so that a
byte can be safely read from or written to the underlying buffer.)

\newthought{To Refine the Shift} operations, we simply check that the
pointer *remains* within the bounds of the buffer, and update the `plen`
to reflect the size remaining after the shift:
\footnotetext{This signature precludes "left" or "backward" shifts; for
that there is an analogous `minusPtr` which we elide for simplicity}

\begin{spec}
plusPtr :: p:Ptr a
        -> o:{ Nat | o <= plen p}   -- in bounds
        -> PtrN b (plen b - o)      -- remaining size 
\end{spec}

\newthought{Types Prevent Overflows} Lets revisit the zero-fill example
from above to understand how the refinements help detect the error:

\begin{code}
exBad = do fp <- mallocForeignPtrBytes 4
           withForeignPtr fp $ \p -> do
             poke (p `plusPtr` 0) zero 
             poke (p `plusPtr` 1) zero 
             poke (p `plusPtr` 2) zero 
             poke (p `plusPtr` 5) zero 
           return fp
        where
           zero = 0 :: Word8
\end{code}


\noindent Lets read the tea leaves for the above error to understand what they say:

\begin{liquiderror}
  Error: Liquid Type Mismatch
   Inferred type
     VV : {VV : Int | VV == ?a && VV == 5}
  
   not a subtype of Required type
     VV : {VV : Int | VV <= plen p}
  
   In Context
     zero : {zero : Word8 | zero == ?b}
     VV   : {VV : Int | VV == ?a && VV == (5  :  int)}
     fp   : {fp : ForeignPtr a | fplen fp == ?c && 0 <= fplen fp}
     ?a   : {fix##63#a : Int | ?a == 5}
     ?c   : {fix##63#c : Int | ?c == 4}
     p    : {p : Ptr a | fplen fp == plen p && ?c <= plen p && ?b <= plen p && zero <= plen p}
     ?b   : {fix##63#b : Integer | ?b == 0}
\end{liquiderror}

\noindent The error says we're bumping `p` up by `VV == 5`
using `plusPtr` but the latter *requires* that bump-offset
be within the size of the buffer referred to by `p`, i.e.
`VV <= plen p`. Indeed, in this context, we have:

\begin{liquiderror}
     p    : {p : Ptr a | fplen fp == plen p && ?c <= plen p && ?b <= plen p && zero <= plen p}
     fp   : {fp : ForeignPtr a | fplen fp == ?c && 0 <= fplen fp}
\end{liquiderror}

\noindent that is, the size of `p`, namely `plen p` equals the size of
`fp`, namely `fplen fp` (thanks to the `withForeignPtr` call), and
finally the latter is equal to `?c` which is `4` bytes. Thus, since
the offset `5` is not less than the buffer size `4`, LiquidHaskell
cannot prove that the call to `plusPtr` is safe, hence the error.
\footnotetext{The alert reader will note that we have strengthened
the type of `plusPtr` to prevent the pointer from wandering outside
the boundary of the buffer. We could instead use a weaker requirement
for `plusPtr` that omits this requirement, and instead have the error
be flagged when the pointer was used to read or write memory.}


Assumptions vs Guarantees
-------------------------

At this point you ought to wonder: where is the *code* for `peek`,
`poke` or `mallocForeignPtrBytes` and so on? How can we know that the
types we assigned to them are in fact legitimate?

Frankly, we can't. This is because those are *externally* implemented
(in this case, in `C`), and hence, invisible to the otherwise
all-seeing eyes of LiquidHaskell. Thus, we are *assuming* or
*trusting* that those functions behave according to their types. Put
another way, the types for the low-level API are our *specification*
for what low-level pointer safety. We shall now *guarantee* that the
higher level modules that build upon this API in fact use the
low-level function in a manner consistent with this specification.

\newthought{Assumptions are a Feature} and not a bug, as they let
us to verify systems that use some modules for which we do not have
the code. Here, we can *assume* a boundary specification, and then
*guarantee* that the rest of the system is safe with respect to
that specification.
\footnotetext{If we so desire, we can also *check* the boundary
specifications at [run-time](wiki-contracts), but that is
outside the scope of LiquidHaskell}.


ByteString API
--------------

Next, lets see how the low-level API can be used to implement
to implement [ByteStrings](bytestring), in a way that lets us
perform fast string operations without opening the door to overflows.

\newthought{Type}


<img src="../img/bytestring.png" height=150px>

\begin{code}
data ByteString = PS {
    bPtr :: ForeignPtr Word8
  , bOff :: !Int
  , bLen :: !Int
  }
\end{code}


\newthought{Refined Type}

<img src="../img/bytestring.png" height=150px>

\begin{code}
{-@ data ByteString = PS {
      bPtr :: ForeignPtr Word8
    , bOff :: {v:Nat| v        <= fplen bPtr}
    , bLen :: {v:Nat| v + bOff <= fplen bPtr}
    }                                       @-}
\end{code}


<img src="../img/bytestring.png" height=150px>

<br>

**A Useful Abbreviation**

\begin{spec}
type ByteStringN N = {v:ByteString| bLen v = N} 
\end{spec}


<div class="hidden">
\begin{code}
{-@ type ByteStringN N = {v:ByteString | bLen v = N} @-}
\end{code}
</div>

\newthought{Legal Bytestrings}


<br>

\begin{code}
{-@ good1 :: IO (ByteStringN 5) @-}
good1 = do fp <- mallocForeignPtrBytes 5
           return (PS fp 0 5)

{-@ good2 :: IO (ByteStringN 3) @-}
good2 = do fp <- mallocForeignPtrBytes 5
           return (PS fp 2 3)
\end{code}

<br>

<div class="fragment">
**Note:** *length* of `good2` is `3` which is *less than* allocated size `5`
</div>

\newthought{Illegal Bytestrings}

<br>

\begin{code}
bad1 = do fp <- mallocForeignPtrBytes 3 
          return (PS fp 0 10)

bad2 = do fp <- mallocForeignPtrBytes 3
          return (PS fp 2 2)
\end{code}

<br>

<div class="fragment">
Claimed length *exceeds* allocation ... **rejected** at compile time
</div>

\newthought{`create`}

<div class="hidden">
\begin{code}
create :: Int -> (Ptr Word8 -> IO ()) -> ByteString
\end{code}
</div>

*Allocate* and *fill* a `ByteString`

<br>

<div class="fragment">
**Specification**
\begin{code}
{-@ create :: n:Nat -> (PtrN Word8 n -> IO ())
           -> ByteStringN n                @-}
\end{code}
</div>


<div class="fragment">
**Implementation**

\begin{code}
create n fill = unsafePerformIO $ do
  fp  <- mallocForeignPtrBytes n
  withForeignPtr fp fill 
  return (PS fp 0 n)
\end{code}
</div>

<!-- CUT
<div class="fragment">
Yikes, there is an error! How to fix?
</div>
-->

\newthought{`pack`}

**Specification**

\begin{code}
{-@ pack :: s:String -> ByteStringN (len s) @-}
\end{code}

<br>

<div class="fragment">

**Implementation**

\begin{code}
pack str      = create n $ \p -> go p xs
  where
  n           = length str
  xs          = map c2w str
  go p (x:xs) = poke p x >> go (plusPtr p 1) xs
  go _ []     = return  ()
\end{code}

</div>



\newthought{`unsafeTake`}

Extract *prefix* string of size `n`

<br>

<div class="fragment">
**Specification**

\begin{code}
{-@ unsafeTake :: n:Nat
               -> b:{ByteString | n <= bLen b}
               -> ByteStringN n            @-}
\end{code}
</div>


<br>

<div class="fragment">
**Implementation**

\begin{code}
unsafeTake n (PS x s l) = PS x s n
\end{code}
</div>

\newthought{`unpack` }

**Specification**

\begin{spec}
unpack 
 :: b:ByteString -> StringN (bLen b)
\end{spec}

<br>

<div class="fragment">
**Implementation**

\begin{spec}
unpack b = you . get . the . idea -- see source 
\end{spec}
</div>

<div class="hidden">
\begin{code}
{-@ qualif Unpack(v:a, acc:b, n:int) : len v = 1 + n + len acc @-}

{-@ unpack :: b:ByteString -> StringN (bLen b) @-}
unpack :: ByteString -> String 
unpack (PS _  _ 0)  = []
unpack (PS ps s l)  = unsafePerformIO $ withForeignPtr ps $ \p ->
   go (p `plusPtr` s) (l - 1)  []
  where
   go p 0 acc = peek p >>= \e -> return (w2c e : acc)
   go p n acc = peek (p `plusPtr` n) >>=   \e -> go p (n-1) (w2c e : acc)
\end{code}

</div>

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

\newthought{HeartBleed Revisited}

Lets revisit our potentially "bleeding" `chop`

<br>

<div class="hidden">
\begin{code}
{-@ type StringN N = {v:String | len v = N} @-}
\end{code}
</div>
<div class="fragment">

\begin{code}
{-@ chop :: s:String
         -> n:{Nat | n <= len s}
         -> StringN n
  @-} 
chop s n =  s'
  where 
    b    = pack s          -- down to low-level
    b'   = unsafeTake n b  -- grab n chars
    s'   = unpack b'       -- up to high-level
\end{code}

<!-- BEGIN CUT 
<br>

Yikes! How shall we fix it?

     END CUT -->
</div>

<!-- BEGIN CUT

A Well Typed `chop`
-------------------

\begin{spec}
{-@ chop :: s:String
         -> n:{Nat | n <= len s}
         -> {v:String | len v = n} @-} 
chop s n = s'
  where 
    b    = pack s          -- down to low-level
    b'   = unsafeTake n b  -- grab n chars
    s'   = unpack b'       -- up to high-level
\end{spec}

END CUT -->

\newthought{"HeartBleed" no more}

<br>

\begin{code}
demo     = [ex6, ex30]
  where
    ex   = ['N','o','r','m','a','n']
    ex6  = chop ex 6  -- ok
    ex30 = chop ex 30  -- out of bounds
\end{code}

<br>

"Bleeding" `chop ex 30` *rejected* by compiler

Nested ByteStrings 
------------------

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

where `ByteStringPair b` describes a pair of `ByteString`s whose
lengths sum to the length of `b`.

\begin{code}
{-@ type ByteStringPair B = (ByteString, ByteString)<{\x1 x2 ->
       bLen x1 + bLen x2 = bLen B}> @-}
\end{code}

Recap: Types Against Overflows
------------------------------

<br>

**Strategy: Specify and Verify Types for**

<br>

1. Low-level `Pointer` API
2. Lib-level `ByteString` API
3. User-level `Application` API

<br>

**Errors at *each* level are prevented by types at *lower* levels**







\begin{comment}
\begin{code}
-----------------------------------------------------------------------
-- Helper Code
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

\end{comment}
