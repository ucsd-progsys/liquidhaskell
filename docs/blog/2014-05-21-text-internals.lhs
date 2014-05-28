---
layout: post
title: "Text Internals"
date: 2014-05-21
comments: true
external-url:
author: Eric Seidel
published: true
categories: benchmarks, text
demo: TextInternal.hs
---

TODO:

1. fix intro segment
2. fix end-segment (why can't we have 3)? shouldn't need qualifiers.
3. tighten up middle bits


So far we have mostly discussed LiquidHaskell in the context of
recursive data structures like lists, but there comes a time in
many programs when you have to put down the list and pick up an
array for the sake of performance.
In this series we're going to examine the `text` library, which
does exactly this in addition to having extensive Unicode support.

`text` is a popular library for efficient text processing.
It provides the high-level API Haskellers have come to expect while
using stream fusion and byte arrays under the hood to guarantee high
performance.

<!--
The thing that makes `text` stand out as an interesting target for
LiquidHaskell, however, is its use of Unicode.
Specifically, `text` uses UTF-16 as its internal encoding, where
each character is represented with either two or four bytes.
We'll see later on how this encoding presents a challenge for
verifying memory-safety, but first let us look at how a `Text`
is represented.

Suppose I want to write a function to get the `Char` at a given index of a
`Text`[^bad].

[^bad]: Disregard for the moment the UTF-8 encoding.
-->

Suppose we wanted to get the *i*th `Char` of a `Text`,
\begin{code} we could write a function[^bad]
charAt (Text a o l) i = word2char $ unsafeIndex a i
  where word2char = chr . fromIntegral
\end{code}
which extracts the underlying array, indexes into it, and casts the `Word16`
to a `Char`, using functions exported by `text`.

[^bad]: This function is bad for numerous reasons, least of which is that `Data.Text.index` is already provided.

\begin{code}Let's try this out in GHCi.
ghci> let t = T.pack "dog"
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

Oh dear, not only did we not get any sort of exception from Haskell, we weren't
even stopped by the OS with a segfault. This is quite dangerous since we have no
idea what sort of data (private keys?) we just read! To be fair to Bryan
O'Sullivan, we did use a function that was clearly marked *unsafe*, but I'd
much rather have the compiler throw an error on these last two calls.

In this post we'll see exactly how prevent invalid memory accesses like this
with LiquidHaskell.

<!-- more -->

<div class="hidden">

\begin{code}
{-# LANGUAGE BangPatterns, MagicHash, Rank2Types,
    RecordWildCards, UnboxedTuples, ExistentialQuantification #-}
{-@ LIQUID "--no-termination" @-}
module TextInternal where

import qualified Control.Exception as Ex
import Control.Monad.ST.Unsafe (unsafeIOToST)
import Data.Bits (shiftR, xor, (.&.))
import Data.Char
import Foreign.C.Types (CSize)
import GHC.Base (Int(..), ByteArray#, MutableByteArray#, newByteArray#,
                 writeWord16Array#, indexWord16Array#, unsafeCoerce#, ord,
                 iShiftL#)
import GHC.ST (ST(..), runST)
import GHC.Word (Word16(..))

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


\begin{code} As an added bonus, the above specification generates **field-accessor measures** that we will use inside types:
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

HEREHEREHEREHERE

A `Nat` is a valid index into an `MArray` if it is less than the number 
of slots, for which we have another type alias `MAValidI`. `text` checks 
this property at run-time, but LiquidHaskell can statically prove that 
the error branch is unreachable.

\begin{code}
{-@ unsafeWrite :: ma:MArray s -> MAValidI ma -> Word16 -> ST s () @-}
\end{code}

A valid index into an `MArray` is a `Nat` that is *strictly* less than
the length of the array.

\begin{code}
{-@ type MAValidI MA = {v:Nat | v < (maLen MA)} @-}
\end{code}

`text` checks this property at run-time, but LiquidHaskell
can statically prove that the error branch is unreachable.

\begin{code}
unsafeWrite MArray{..} i@(I# i#) (W16# e#)
  | i < 0 || i >= maLen = liquidError "out of bounds"
  | otherwise = ST $ \s1# ->
      case writeWord16Array# maBA i# e# s1# of
        s2# -> (# s2#, () #)
\end{code}

So now we can write individual `Word16`s into an array, but maybe we
have a whole bunch of text we want to dump into the array. Remember,
`text` is supposed to be fast!
C has `memcpy` for cases like this but it's notoriously unsafe; with
the right type however, we can regain safety. `text` provides a wrapper around
`memcpy` to copy `n` elements from one `MArray` to another.

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

You might notice the two `assert`s in the function, they were in the
original code as run-time checks of the precondition, but LiquidHaskell
can actually *prove* that the `assert`s **cannot** fail, we just have
to give `assert` the type

\begin{code}
{-@ assert assert :: {v:Bool | (Prop v)} -> a -> a @-}
\end{code}

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
  | i < 0 || i >= aLen = liquidError "out of bounds"
  | otherwise = case indexWord16Array# aBA i# of
                  r# -> (W16# r#)
\end{code}

As before, LiquidHaskell can easily prove that the error branch
is unreachable, i.e. is *never* executed at run-time.

Wrapping it all up
------------------

Now we can finally define the core datatype of the `text` package!
A `Text` value consists of three fields, an `Array` and

A. an `Int` offset into the *middle* of the array, and

B. an `Int` length denoting the number of valid bytes *after* the offset.

We can specify the invariants (A) and (B) via the refined type:

\begin{code}
{-@ data Text 
    = Text { tarr :: Array
           , toff :: {v:Nat | v      <= (aLen tarr)}
           , tlen :: {v:Nat | v+toff <= (aLen tarr)}
           }                                            @-}
\end{code}

These invariants ensure that any *index* we pick between `off` and
`off + len` will be a valid index into `arr`. 

RJ: Insert "dog" bit here.
RJ: How come we don't use "offset" at all?


Lets take a quick step back and recall the example
that motivated this whole discussion.

\begin{code}
charAt (Text a o l) i = word2char $ unsafeIndex a i
  where word2char = chr . fromIntegral
\end{code}

Fantastic! LiquidHaskell is telling us that our call to
`unsafeIndex` is, in fact, **unsafe** because we don't know
that `i` is a valid index.


<!--

If you're not quite convinced, consider the following `Text`s.
![the layout of multiple Texts](/images/text-layout.png)
<div style="width:80%; text-align:center; margin:auto; margin-bottom:1em;"><p>Multiple valid <code>Text</code> configurations, all using an <code>Array</code> with 10 slots. The valid slots are shaded. Note that the key invariant is that <code>off + len <= aLen</code>.</p></div>

-->

RJ: RECAP


That was a lot for one day; next time we'll take a look at how to handle uncode in `text`.





