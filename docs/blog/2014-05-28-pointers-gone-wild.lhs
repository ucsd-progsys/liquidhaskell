---
layout: post
title: "Pointers Gone Wild"
date: 2014-05-28
comments: true
external-url:
author: Eric Seidel
published: true
categories: benchmarks, text
demo: TextInternal.hs
---

A large part of the allure of Haskell is its elegant, high-level ADTs
that ensure[^compilercorrectness] that programs won't be plagued by problems
like the infamous [SSL heartbleed bug](http://en.wikipedia.org/wiki/Heartbleed).

[^compilercorrectness]: Assuming the absence of errors in the compiler and run-time...

However, another part of Haskell's charm is that when you really really 
need to, you can drop down to low-level pointer twiddling to squeeze the 
most performance out of your machine. But of course, that opens the door 
to the #heartbleeds.

Can we have have our cake and eat it too? 

Can we twiddle pointers and still get the nice safety assurances of high-level types?

<!-- more -->

To understand the potential for potential bleeding,
let's study the popular `text` library for efficient 
text processing. The library provides the high-level 
API Haskellers have come to expect while using stream 
fusion and byte arrays under the hood to guarantee 
high performance.

Suppose we wanted to get the *i*th `Char` of a `Text`,
\begin{code} we could write a function[^bad]
charAt (Text a o l) i = word2char $ unsafeIndex a (o+i)
  where 
    word2char         = chr . fromIntegral
\end{code}
which extracts the underlying array `a`, indexes into it starting
at the offset `o` and casts the `Word16` to a `Char`, using 
functions exported by `text`.

[^bad]: This function is bad for numerous reasons, least of which is that `Data.Text.index` is already provided, but stay with us...

\begin{code}Let's try this out in GHCi.
ghci> let t = pack ['d','o','g']
ghci> charAt t 0
'd'
ghci> charAt t 2
'g'
\end{code}

\begin{code}Looks good so far, what happens if we keep going?
ghci> charAt t 3
'\NUL'
ghci> charAt t 100
'\8745'
\end{code}

Oh dear, not only did we not get any sort of exception from Haskell, 
we weren't even stopped by the OS with a segfault. This is quite 
dangerous since we have no idea what sort of data we just read! 
To be fair to the library's authors, we did use a function that 
was clearly branded `unsafe`, but these functions, while not 
intended for *clients*, pervade the implementation of the *library*.

Wouldn't it be nice to have these last two calls *rejected at compile time*?

In this post we'll see exactly how prevent invalid memory accesses 
like this with LiquidHaskell.


<div class="hidden">

\begin{code}
{-# LANGUAGE BangPatterns, MagicHash, Rank2Types,
    RecordWildCards, UnboxedTuples, ExistentialQuantification #-}
{-@ LIQUID "--no-termination" @-}
module TextInternal (test, goodMain, badMain, charAt, charAt') where

import qualified Control.Exception as Ex
import Control.Applicative     ((<$>))
import Control.Monad           (when)
import Control.Monad.ST.Unsafe (unsafeIOToST)
import Data.Bits (shiftR, xor, (.&.))
import Data.Char
import Foreign.C.Types (CSize)
import GHC.Base (Int(..), ByteArray#, MutableByteArray#, newByteArray#,
                 writeWord16Array#, indexWord16Array#, unsafeCoerce#, ord,
                 iShiftL#)
import GHC.ST (ST(..), runST)
import GHC.Word (Word16(..))

import qualified Data.Text.Lazy.IO as TIO
import qualified Data.Text as T
import qualified Data.Text.Internal as T

import Language.Haskell.Liquid.Prelude

{-@ aLen :: a:Array -> {v:Nat | v = (aLen a)}  @-}

{-@ maLen :: a:MArray s -> {v:Nat | v = (maLen a)}  @-}

new          :: forall s. Int -> ST s (MArray s)
unsafeWrite  :: MArray s -> Int -> Word16 -> ST s ()
unsafeFreeze :: MArray s -> ST s Array
unsafeIndex  :: Array -> Int -> Word16
copyM        :: MArray s               -- ^ Destination
             -> Int                    -- ^ Destination offset
             -> MArray s               -- ^ Source
             -> Int                    -- ^ Source offset
             -> Int                    -- ^ Count
             -> ST s ()

{-@ memcpyM :: MutableByteArray# s -> CSize -> MutableByteArray# s -> CSize -> CSize -> IO () @-}
memcpyM :: MutableByteArray# s -> CSize -> MutableByteArray# s -> CSize -> CSize -> IO ()
memcpyM = undefined

--------------------------------------------------------------------------------
--- Helper Code
--------------------------------------------------------------------------------
{-@ shiftL :: i:Nat -> n:Nat -> {v:Nat | ((n = 1) => (v = (i * 2)))} @-}
shiftL :: Int -> Int -> Int
shiftL = undefined -- (I# x#) (I# i#) = I# (x# `iShiftL#` i#)

pack :: String -> Text
pack = undefined -- not "actually" using

assert b a = Ex.assert b a


data Text = Text Array Int Int

{-@ tLength :: t:Text -> {v:_ | v = (tLen t)} @-}
tLength (Text _ _ n)  =  n
\end{code}

</div>

The `Text` Lifecycle
--------------------
`text` splits the reading and writing array operations between two
types of arrays, immutable `Array`s and mutable `MArray`s. This leads to
the following general lifecycle:

![The lifecycle of a `Text`](/images/text-lifecycle.png)

The main four array operations we care about are:

1. **creating** an `MArray`,
2. **writing** into an `MArray`,
3. **freezing** an `MArray` into an `Array`, and
4. **reading** from an `Array`.

Creating an `MArray`
--------------------

The (mutable) `MArray` is a thin wrapper around GHC's primitive
`MutableByteArray#`, additionally carrying the number of `Word16`s it
can store.

\begin{code}
data MArray s = MArray { maBA  :: MutableByteArray# s
                       , maLen :: !Int
                       }
\end{code}

It doesn't make any sense to have a negative length, so we *refine*
the data definition to require that `maLen` be non-negative. 

\begin{code}
{-@ data MArray s = MArray { maBA  :: MutableByteArray# s
                           , maLen :: Nat
                           }
  @-}
\end{code}


\begin{code} As an added bonus, the above specification generates **field-accessor measures** that we will use inside the refined types:
{-@ measure maLen :: MArray s -> Int
    maLen (MArray a l) = l
  @-}
\end{code}

We can use these accessor measures to define `MArray`s of size `N`:

\begin{code}
{-@ type MArrayN a N = {v:MArray a | (maLen v) = N} @-}
\end{code}

and we can use the above alias, to write a type that tracks the size
of an `MArray` at the point where it is created:

\begin{code}
{-@ new :: forall s. n:Nat -> ST s (MArrayN s n) @-}
new n
  | n < 0 || n .&. highBit /= 0 = error "size overflow"
  | otherwise = ST $ \s1# ->
       case newByteArray# len# s1# of
         (# s2#, marr# #) -> (# s2#, MArray marr# n #)
  where !(I# len#) = bytesInArray n
        highBit    = maxBound `xor` (maxBound `shiftR` 1)
        bytesInArray n = n `shiftL` 1
\end{code}

`new n` is an `ST` action that produces an `MArray s` with `n` slots each 
of which is 2 bytes (as internally `text` manipulates `Word16`s).

The verification process here is quite simple; LH recognizes that 
the `n` used to construct the returned array (`MArray marr# n`) 
the same `n` passed to `new`. 

Writing into an `MArray`
------------------------

Once we have *created* an `MArray`, we'll want to write our data into it. 

A `Nat` is a valid index into an `MArray` if it is *strictly less than* 
the size of the array.

\begin{code}
{-@ type MAValidI MA = {v:Nat | v < (maLen MA)} @-}
\end{code}

We use this valid index alias to refine the type of `unsafeWrite`

\begin{code}
{-@ unsafeWrite :: ma:MArray s -> MAValidI ma -> Word16 -> ST s () @-}
unsafeWrite MArray{..} i@(I# i#) (W16# e#)
  | i < 0 || i >= maLen = assert False $ error "out of bounds"
  | otherwise = ST $ \s1# ->
      case writeWord16Array# maBA i# e# s1# of
        s2# -> (# s2#, () #)
\end{code}

Note that, when compiled with appropriate options, the implementation of
`text` checks the bounds at run-time. However, LiquidHaskell can statically
prove that the error branch is unreachable, i.e. the `assert` **cannot fail**
(as long as the inputs adhere to the given specification) by giving `assert`
the type:

\begin{code}
{-@ assert assert :: {v:Bool | (Prop v)} -> a -> a @-}
\end{code}

Bulk Writing into an `MArray`
-----------------------------

So now we can write individual `Word16`s into an array, but maybe we
have a whole bunch of text we want to dump into the array. Remember,
`text` is supposed to be fast! C has `memcpy` for cases like this but 
it's notoriously unsafe; with the right type however, we can regain safety. 
`text` provides a wrapper around `memcpy` to copy `n` elements from 
one `MArray` to another.

`copyM` requires two `MArray`s and valid offsets into each -- note
that a valid offset is **not** necessarily a valid *index*, it may
be one element out-of-bounds

\begin{code}
{-@ type MAValidO MA = {v:Nat | v <= (maLen MA)} @-}
\end{code}

-- and a `count` of elements to copy.
The `count` must represent a valid region in each `MArray`, in
other words `offset + count <= length` must hold for each array.

\begin{code}
{-@ copyM :: dest:MArray s
          -> didx:MAValidO dest
          -> src:MArray s
          -> sidx:MAValidO src
          -> {v:Nat | (((didx + v) <= (maLen dest))
                    && ((sidx + v) <= (maLen src)))}
          -> ST s ()
  @-}
copyM dest didx src sidx count
    | count <= 0 = return ()
    | otherwise =
    assert (sidx + count <= maLen src) .
    assert (didx + count <= maLen dest) .
    unsafeIOToST $ memcpyM (maBA dest) (fromIntegral didx)
                           (maBA src) (fromIntegral sidx)
                           (fromIntegral count)
\end{code}

Again, the two `assert`s in the function were in the original code as 
(optionally compiled out) run-time checks of the precondition, but with 
LiquidHaskell we can actually *prove* that the `assert`s **always succeed**.

Freezing an `MArray` into an `Array`
------------------------------------

Before we can package up our `MArray` into a `Text`, we need to
*freeze* it, preventing any further mutation. The key property 
here is of course that the frozen `Array` should have the same 
length as the `MArray`.

Just as `MArray` wraps a mutable array, `Array` wraps an *immutable*
`ByteArray#` and carries its length in `Word16`s.

\begin{code}
data Array = Array { aBA  :: ByteArray#
                   , aLen :: !Int
                   }
\end{code}

As before, we get free accessor measures `aBA` and `aLen` just by
refining the data definition

\begin{code}
{-@ data Array = Array { aBA  :: ByteArray#
                       , aLen :: Nat
                       }
  @-}
\end{code}

so we can refer to the components of an `Array` in our refinements.
Using these measures, we can define

\begin{code}
{-@ type ArrayN N = {v:Array | (aLen v) = N} @-}
{-@ unsafeFreeze :: ma:MArray s -> ST s (ArrayN (maLen ma)) @-}
unsafeFreeze MArray{..} = ST $ \s# ->
                          (# s#, Array (unsafeCoerce# maBA) maLen #)
\end{code}

Again, LiquidHaskell is happy to prove our specification as we simply
copy the length parameter `maLen` over into the `Array`.

Reading from an `Array`
------------------------
Finally, we will eventually want to read a value out of the
`Array`. As with `unsafeWrite` we require a valid index into the
`Array`, which we denote using the `AValidI` alias.

\begin{code}
{-@ type AValidI A = {v:Nat | v < (aLen A)} @-}
{-@ unsafeIndex :: a:Array -> AValidI a -> Word16 @-}
unsafeIndex Array{..} i@(I# i#)
  | i < 0 || i >= aLen = assert False $ error "out of bounds"
  | otherwise = case indexWord16Array# aBA i# of
                  r# -> (W16# r#)
\end{code}

As before, LiquidHaskell can easily prove that the error branch
is unreachable, i.e. is *never* executed at run-time.

Wrapping it all up
------------------

Now we can finally define the core datatype of the `text` package!
A `Text` value consists of three fields:

A. an `Array`,

B. an `Int` offset into the *middle* of the array, and

C. an `Int` length denoting the number of valid indices *after* the offset.

We can specify the invariants for fields (b) and (c) with the refined type:

\begin{code}
{-@ data Text
      = Text { tArr :: Array
             , tOff :: {v:Nat | v      <= (aLen tArr)}
             , tLen :: {v:Nat | v+tOff <= (aLen tArr)}
             }
  @-}
\end{code}

These invariants ensure that any *index* we pick between `tOff` and
`tOff + tLen` will be a valid index into `tArr`. 

As shown above with `new`, `unsafeWrite`, and `unsafeFreeze`, we can type the
top-level function that creates a `Text` from a `[Char]` as:

\begin{code}
{-@ pack :: s:String -> {v:Text | (tLen v) = (len s)} @-}
\end{code}

Preventing Bleeds
-----------------

Now, let us close the circle and return to potentially *bleeding* function:

\begin{code}
charAt' (Text a o l) i = word2char $ unsafeIndex a (o+i)
  where 
    word2char          = chr . fromIntegral
\end{code}

Aha! LiquidHaskell flags the call to `unsafeIndex` because of course, `i` may fall
outside the bounds of the given array `a`! We can remedy that by specifying
a bound for the index:

\begin{code}
{-@ charAt :: t:Text -> {v:Nat | v < (tLen t)} -> Char @-}
charAt (Text a o l) i = word2char $ unsafeIndex a (o+i)
  where 
    word2char         = chr . fromIntegral
\end{code}

That is, we can access the `i`th `Char` as long as `i` is a `Nat` less
than the the size of the text, namely `tLen t`. Now LiquidHaskell is convinced
that the call to `unsafeIndex` is safe, but of course, we have passed
the burden of proof onto users of `charAt`.

Now, if we try calling `charAt` as we did at the beginning

\begin{code}
test = [good,bad]
  where
    dog  = ['d','o','g']
    good = charAt (pack dog) 2
    bad  = charAt (pack dog) 3
\end{code}

we see that LiquidHaskell verifies the `good` call, but flags `bad` as
**unsafe**.

Enforcing Sanitization
----------------------

EDIT: As several folks have pointed out, the #heartbleed error was
due to inputs not being properly sanitized. The above approach 
**ensures, at compile time**, that proper sanitization has been 
performed. 

To see this in action, lets write a little function that just shows the 
character at a given position:

\begin{code}
{-@ showCharAt :: t:_ -> {v:Nat | v < (tLen t)} -> _ @-}
showCharAt t i = putStrLn $ show $ charAt t i
\end{code}

Now, the following function, that correctly sanitizes is **accepted**

\begin{code}
goodMain :: IO ()
goodMain 
  = do txt <- pack <$> getLine
       i   <- readLn
       if 0 <= i && i < tLength txt 
         then showCharAt txt i 
         else putStrLn "Bad Input!"
\end{code}

but this function, which has insufficient sanitization, is **rejected**

\begin{code}
badMain :: IO ()
badMain 
  = do txt <- pack <$> getLine 
       i   <- readLn
       if 0 <= i 
         then showCharAt txt i 
         else putStrLn "Bad Input!"
\end{code}

Thus, we can use LiquidHaskell to block, at compile time, any serious bleeding
from pointers gone wild.
