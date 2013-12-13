---
layout: post
title: "Text Internals"
date:
comments: true
external-url:
author: Eric Seidel
published: false
categories: benchmarks, text
demo: TextInternal.hs
---

So far we have mostly discussed LiquidHaskell in the context of
recursive data structures like lists, but there comes a time in many
programs when you have to put down the list and pick up an array for
the sake of performance. In this series we're going to examine the
`text` library, which does exactly this in addition to having
extensive Unicode support.

`text` is a popular library for efficient text processing. It provides
the high-level API haskellers have come to expect while using stream
fusion and byte arrays under the hood to guarantee high
performance. The thing that makes `text` stand out as an interesting
target for LiquidHaskell, however, is its use of
Unicode. Specifically, `text` uses UTF-16 as its internal encoding,
where each character is represented with either two or four
bytes. We'll see later on how this encoding presents a challenge for
verifying memory-safety, but first let us look at how a `Text` is
represented.

<!-- more -->

\begin{code}
{-# LANGUAGE BangPatterns, CPP, MagicHash, Rank2Types,
    RecordWildCards, UnboxedTuples #-}
module TextInternal where

import Control.Monad.ST.Unsafe (unsafeIOToST)
import Data.Bits (shiftL, shiftR, xor, (.&.))
import Foreign.C.Types (CSize)
import GHC.Base (Int(..), ByteArray#, MutableByteArray#, newByteArray#,
                 writeWord16Array#, indexWord16Array#, unsafeCoerce#)
import GHC.ST (ST(..), runST)
import GHC.Word (Word16(..))

import Language.Haskell.Liquid.Prelude
\end{code}

`text` uses two types of arrays internally, immutable `Array`s and
mutable `MArray`s.

\begin{code}
data Array = Array {
    aBA  :: ByteArray#
  , aLen :: !Int
  }
{-@ data Array = Array { aBA :: ByteArray#, aLen :: Nat } @-}
{-@ measure alen :: Array -> Int
    alen (Array aBA aLen) = aLen
  @-}
{-@ aLen :: a:Array -> {v:Nat | v = (alen a)}  @-}

data MArray s = MArray {
    maBA :: MutableByteArray# s
  , maLen :: !Int
  }
{-@ data MArray s = MArray { maBA :: MutableByteArray# s, maLen :: Nat } @-}
{-@ measure malen :: MArray s -> Int
    malen (MArray maBA maLen) = maLen
  @-}
{-@ maLen :: a:MArray s -> {v:Nat | v = (malen a)}  @-}
\end{code}

Both types carry around with them the number of `Word16`s they can
hold (this is actually only true when you compile with asserts turned
on, but we use this to ease the verification process).

The main three array operations we care about are: (1) writing into an
`MArray`, (2) reading from an `Array`, and (3) *freezing* an `MArray`
into an `Array`. But first, let's see how one creates an `MArray`.

\begin{code}
{-@ type MArrayN s N = {v:MArray s | (malen v) = N} @-}
{-@ new :: forall s. n:Nat -> ST s (MArrayN s n) @-}
new :: forall s. Int -> ST s (MArray s)
new n
  | n < 0 || n .&. highBit /= 0 = error $ "Data.Text.Array.new: size overflow"
  | otherwise = ST $ \s1# ->
       case newByteArray# len# s1# of
         (# s2#, marr# #) -> (# s2#, MArray marr# n #)
  where !(I# len#) = bytesInArray n
        highBit    = maxBound `xor` (maxBound `shiftR` 1)
        bytesInArray n = n `shiftL` 1
\end{code}

`new n` is an `ST` action that produces an `MArray s` with `n` slots,
denoted by the type alias `MArrayN s n`. Note that we are not talking
about bytes here, `text` deals with `Word16`s internally and as such
we actualy allocate `2*n` bytes.  While this may seem like a lof of
code to just create an array, the verification process here is quite
simple. LiquidHaskell simply recognizes that the `n` used to construct
the returned array (`MArray marr# n`) is the same `n` passed to
`new`. It should be noted that we're abstracting away some detail here
with respect to the underlying `MutableByteArray#`, specifically we're
making the assumption that any *unsafe* operation will be caught and
dealt with before the `MutableByteArray#` is touched.

Once we have an `MArray` in hand, we'll want to be able to write our
data into it. A `Nat` is a valid index into an `MArray` `ma` if it is
less than the number of slots, for which we have another type alias
`MAValidI ma`. `text` includes run-time assertions that check this
property, but LiquidHaskell can statically prove the assertions will
always pass.

\begin{code}
{-@ type MAValidI MA = {v:Nat | v < (malen MA)} @-}
{-@ unsafeWrite :: ma:MArray s -> MAValidI ma -> Word16 -> ST s () @-}
unsafeWrite :: MArray s -> Int -> Word16 -> ST s ()
unsafeWrite MArray{..} i@(I# i#) (W16# e#)
  | i < 0 || i >= maLen = liquidError "out of bounds"
  | otherwise = ST $ \s1# ->
      case writeWord16Array# maBA i# e# s1# of
        s2# -> (# s2#, () #)
\end{code}

Before we can package up our `MArray` into a `Text`, we need to
*freeze* it, preventing any further mutation. The key property here is
of course that the frozen `Array` should have the same length as the
`MArray`.

\begin{code}
{-@ type ArrayN N = {v:Array | (alen v) = N} @-}
{-@ unsafeFreeze :: ma:MArray s -> ST s (ArrayN (malen ma)) @-}
unsafeFreeze :: MArray s -> ST s Array
unsafeFreeze MArray{..} = ST $ \s# ->
                          (# s#, Array (unsafeCoerce# maBA) maLen #)
\end{code}

Again, LiquidHaskell is happy to prove our specification as we simply
copy the length parameter `maLen` over into the `Array`.

Finally, we will eventually want to read a value out of the
`Array`. As with `unsafeWrite` we require a valid index into the
`Array`, which we denote using the `AValidI` alias.

\begin{code}
{-@ type AValidI A = {v:Nat | v < (alen A)} @-}
{-@ unsafeIndex :: a:Array -> AValidI a -> Word16 @-}
unsafeIndex :: Array -> Int -> Word16
unsafeIndex Array{..} i@(I# i#)
  | i < 0 || i >= aLen = liquidError "out of bounds"
  | otherwise = case indexWord16Array# aBA i# of
                  r# -> (W16# r#)
\end{code}

As before, LiquidHaskell can easily prove that the run-time assertions
will never fail.

But what if we want to copy a region of one array into another? Well, we could
repeatedly `unsafeWrite` the result of `unsafeIndex`ing, but `text` is designed
to be fast. C has `memcpy` for cases like this but it's notoriously unsafe; with
the right type however, we can regain safety. `text` provides a wrapper around
`memcpy` to copy `n` elements from one `MArray` to another.

\begin{code}
{-@ type MAValidO MA = {v:Nat | v <= (malen MA)} @-}
{-@ copyM :: dst:MArray s -> didx:MAValidO dst
          -> src:MArray s -> sidx:MAValidO src
          -> {v:Nat | (((v + didx) <= (malen dst))
                    && ((v + sidx) <= (malen src)))}
          -> ST s ()
  @-}
copyM :: MArray s               -- ^ Destination
      -> Int                    -- ^ Destination offset
      -> MArray s               -- ^ Source
      -> Int                    -- ^ Source offset
      -> Int                    -- ^ Count
      -> ST s ()
copyM dest didx src sidx count
    | count <= 0 = return ()
    | otherwise =
    liquidAssert (sidx + count <= maLen src) .
    liquidAssert (didx + count <= maLen dest) .
    unsafeIOToST $ memcpyM (maBA dest) (fromIntegral didx)
                           (maBA src) (fromIntegral sidx)
                           (fromIntegral count)
\end{code}

`copyM` requires two `MArray`s and valid offsets into each -- note that a valid
offset is **not** necessarily a valid *index*, it may be one element
out-of-bounds -- and a `count` of elements to copy. The `count` must represent a
valid region in each `MArray`, in other words `offset + count <= length` must
hold for each array. `memcpyM` is an FFI function writen in C, which we don't
currently support, so we simply leave it `undefined`.

\begin{code}
{-@ memcpyM :: MutableByteArray# s -> CSize -> MutableByteArray# s -> CSize -> CSize -> IO () @-}
memcpyM :: MutableByteArray# s -> CSize -> MutableByteArray# s -> CSize -> CSize -> IO ()
memcpyM = undefined
\end{code}

Now we can finally define the core datatype of the `text` package! A `Text`
value consists of an *array*, an *offset*, and a *length*. The offset and length
are `Nat`s satisfying two properties: (1) `off <= alen arr` and (2)
`off + len <= alen arr`. These invariants ensure that any *index* we pick
between `off` and `off + len` will be a valid index into `arr`.

\begin{code}
data Text = Text Array Int Int
{-@ data Text [tlen] = Text (arr :: Array)
                            (off :: TValidO arr)
                            (len :: TValidL off arr)
  @-}

{-@ measure tarr :: Text -> Array
    tarr (Text a o l) = a
  @-}
{-@ measure toff :: Text -> Int
    toff (Text a o l) = o
  @-}
{-@ measure tlen :: Text -> Int
    tlen (Text a o l) = l
  @-}
\end{code}

The liquid-type for `Text` makes use of the following two type-aliases to
express the core invariant.

\begin{code}
{-@ type TValidO A   = {v:Nat | v     <= (alen A)} @-}
{-@ type TValidL O A = {v:Nat | (v+O) <= (alen A)} @-}
\end{code}

Stay tuned, next time we'll show how we can use these low-level
operations to verify the safety of the API that `text` actually
exposes to the user.
