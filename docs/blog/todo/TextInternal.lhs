---
layout: post
title: "Text Internals"
date:
comments: true
external-url:
author: Eric Seidel
published: false
categories: benchmarks
demo: TextInternal.hs
---

In the past we've seen how to use LiquidHaskell to...

In this series we will use LiquidHaskell to verify the safety of low-level
operations like array index and update.

The `text` library is commonly used when one cares about processing lots
of text in a time-efficient manner. Its performance is better than the standard
`String` type because `text` uses a byte-array representation rather than a list
of characters.

<!-- more -->

\begin{code}
{-# LANGUAGE BangPatterns, CPP, MagicHash, Rank2Types,
    RecordWildCards, UnboxedTuples #-}
module TextInternal where

import Control.Monad.ST.Unsafe
import Data.Bits
import Foreign.C.Types
import GHC.Base
import GHC.ST
import GHC.Word

import Language.Haskell.Liquid.Prelude

# define CHECK_BOUNDS(_func_,_len_,_k_) \
if (_k_) < 0 || (_k_) >= (_len_) then error ("Data.Text.Array." ++ (_func_) ++ ": bounds error, offset " ++ show (_k_) ++ ", length " ++ show (_len_)) else
\end{code}

Arrays
------

There are two types of arrays, mutable `MArray`s and immutable `Array`s.

\begin{code}
{-@ data Array = Array (aBA :: ByteArray#) (aLen :: Nat) @-}
data Array = Array {
    aBA  :: ByteArray#
  , aLen :: !Int
  }
{-@ measure alen :: Array -> Int
    alen (Array aBA aLen) = aLen
  @-}
{-@ aLen :: a:Array -> {v:Nat | v = (alen a)}  @-}

{-@ data MArray s = MArray (maBA :: MutableByteArray# s) (maLen :: Nat) @-}
data MArray s = MArray {
    maBA :: MutableByteArray# s
  , maLen :: !Int
  }
{-@ measure malen :: MArray s -> Int
    malen (MArray maBA maLen) = maLen
  @-}
{-@ maLen :: a:MArray s -> {v:Nat | v = (malen a)}  @-}
\end{code}

All `Array`s start off mutable and are eventually *frozen* before they are
packaged into a `Text`.

\begin{code}
{- GHC.Prim.newByteArray# :: l:Int# -> GHC.Prim.State# s
      -> (# GHC.Prim.State# s, {v:MutableByteArray# s | (mbalen v) = l} #)
  @-}

{-@ type ArrayN    N = {v:Array    | (alen v)  = N} @-}
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

That might seem a lot of code to just create an array but don't worry, the
verification process here is quite simple. LiquidHaskell simply recognizes
that the `n` used to construct the returned array (`MArray marr# n`) is the
same `n` passed to `new`. It should be noted that we're abstracting away some
detail here with respect to the underlying `MutableByteArray#`, specifically
we're making the assumption that any *unsafe* operation will be caught and
dealt with before the `MutableByteArray#` is touched.

The only way to produce an immutable `Array` is to *freeze* an `MArray`.

\begin{code}
{-@ unsafeFreeze :: ma:MArray s -> ST s (ArrayN (malen ma)) @-}
unsafeFreeze :: MArray s -> ST s Array
unsafeFreeze MArray{..} = ST $ \s# ->
                          (# s#, Array (unsafeCoerce# maBA) maLen #)

{-@ qualif FreezeMArr(v:Array, ma:MArray s):
        alen(v) = malen(ma)
  @-}

{-@ empty :: {v:Array | (alen v) = 0}  @-}
empty :: Array
empty = runST (new 0 >>= unsafeFreeze)
\end{code}

Again, LiquidHaskell is happy to verify that `unsafeFreeze` returns an
`Array` with length equal to the input `MArray` as we simply copy the
length parameter `maLen` over.


Operating on Arrays
-------------------

There are two basic operations we might want to perform on an array, indexing
and writing.

Naturally, we can only write a value into an `MArray` and we require a valid
index to perform the write, i.e. a `Nat` that is less than the length of the
array.

\begin{code}
{-@ type MAValidI A = {v:Nat | v < (malen A)} @-}

{-@ unsafeWrite :: ma:MArray s -> MAValidI ma -> Word16 -> ST s () @-}
unsafeWrite :: MArray s -> Int -> Word16 -> ST s ()
unsafeWrite MArray{..} i@(I# i#) (W16# e#) = ST $ \s1# ->
  CHECK_BOUNDS("unsafeWrite",maLen,i)
  case writeWord16Array# maBA i# e# s1# of
    s2# -> (# s2#, () #)
\end{code}

Indexing, on the other hand, is only allowed once the array has been
frozen and, as you might expect, also requires the index to be within
bounds of the array.

\begin{code}
{-@ type AValidI A   = {v:Nat | v     <  (alen A)} @-}
{-@ type AValidO A   = {v:Nat | v     <= (alen A)} @-}
{-@ type AValidL O A = {v:Nat | (v+O) <= (alen A)} @-}

{-@ unsafeIndex :: a:Array -> AValidI a -> Word16 @-}
unsafeIndex :: Array -> Int -> Word16
unsafeIndex Array{..} i@(I# i#) =
  CHECK_BOUNDS("unsafeIndex",aLen,i)
  case indexWord16Array# aBA i# of r# -> (W16# r#)
\end{code}

But what if we want to copy a region of one array into another? Well, we could
repeatedly `unsafeWrite` the result of `unsafeIndex`ing, but `text` is designed
to be fast. C has `memcpy` for cases like this but it's notoriously unsafe; with
the right type however, we can regain safety. `text` provides a wrapper around
`memcpy` to copy `n` elements from one `MArray` to another.

\begin{code}
{-@ type MAValidO A   = {v:Nat | v     <= (malen A)} @-}
{-@ type MAValidL O A = {v:Nat | (v+O) <= (malen A)} @-}

{-@ qualif MALen(v:Int, a:MArray s): v = malen(a) @-}
{-@ qualif MALen(v:MArray s, i:Int): i = malen(v) @-}

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
between `off` and `len` will be a valid index into `arr`.

\begin{code}
{-@ data Text [tlen] = Text (arr :: Array)
                            (off :: TValidO arr)
                            (len :: TValidL off arr)
  @-}
data Text = Text Array Int Int

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
