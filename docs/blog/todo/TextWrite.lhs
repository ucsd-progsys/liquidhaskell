---
layout: post
title: "Text Write"
date: 2014-02-23
comments: true
external-url:
author: Eric Seidel
published: false
categories: benchmarks, text
demo: TextWrite.hs
---

Last time, we showed how to reason about Unicode and a variable-width
encoding of `Char`s when consuming a `Text` value, today we'll look at
the same issue from the perspective of *building* a `Text`.

<!-- more -->

<div class="hidden">

\begin{code}
{-# LANGUAGE BangPatterns, CPP, MagicHash, Rank2Types,
    RecordWildCards, UnboxedTuples, ExistentialQuantification #-}
{-@ LIQUID "--no-termination" @-}
module TextWrite where

import Control.Monad.ST.Unsafe (unsafeIOToST)
import Foreign.C.Types (CSize)
import GHC.Base hiding (unsafeChr)
import GHC.ST
import GHC.Word (Word16(..))
import Data.Bits hiding (shiftL)
import Data.Word

import Language.Haskell.Liquid.Prelude

--------------------------------------------------------------------------------
--- From TextInternal
--------------------------------------------------------------------------------

{-@ shiftL :: i:Nat -> n:Nat -> {v:Nat | ((n = 1) => (v = (i * 2)))} @-}
shiftL :: Int -> Int -> Int
shiftL = undefined -- (I# x#) (I# i#) = I# (x# `iShiftL#` i#)

{-@ measure isUnknown :: Size -> Prop
    isUnknown (Exact n) = false
    isUnknown (Max   n) = false
    isUnknown (Unknown) = true
  @-}
{-@ measure getSize :: Size -> Int
    getSize (Exact n) = n
    getSize (Max   n) = n
  @-}

{-@ invariant {v:Size | (getSize v) >= 0} @-}

data Size = Exact {-# UNPACK #-} !Int -- ^ Exact size.
          | Max   {-# UNPACK #-} !Int -- ^ Upper bound on size.
          | Unknown                   -- ^ Unknown size.
            deriving (Eq, Show)

{-@ upperBound :: k:Nat -> s:Size -> {v:Nat | v = ((isUnknown s) ? k : (getSize s))} @-}
upperBound :: Int -> Size -> Int
upperBound _ (Exact n) = n
upperBound _ (Max   n) = n
upperBound k _         = k

data Step s a = Done
              | Skip !s
              | Yield !a !s

data Stream a =
    forall s. Stream
    (s -> Step s a)             -- stepper function
    !s                          -- current state
    !Size                       -- size hint

{-@ data Array = Array { aBA  :: ByteArray#
                       , aLen :: Nat 
                       } 
  @-}

data Array = Array {
    aBA  :: ByteArray#
  , aLen :: !Int
  }

{-@ measure alen     :: Array -> Int
    alen (Array a n) = n
  @-}

{-@ aLen :: a:Array -> {v:Nat | v = (alen a)}  @-}

{-@ type ArrayN  N   = {v:Array | (alen v) = N} @-}

{-@ type AValidI A   = {v:Nat | v     <  (alen A)} @-}
{-@ type AValidO A   = {v:Nat | v     <= (alen A)} @-}
{-@ type AValidL O A = {v:Nat | (v+O) <= (alen A)} @-}

{-@ data MArray s = MArray { maBA  :: MutableByteArray# s
                           , maLen :: Nat } @-}

data MArray s = MArray {
    maBA  :: MutableByteArray# s
  , maLen :: !Int
  }

{-@ measure malen :: MArray s -> Int
    malen (MArray a n) = n
  @-}

{-@ maLen :: a:MArray s -> {v:Nat | v = (malen a)}  @-}

{-@ type MArrayN s N = {v:MArray s | (malen v) = N} @-}

{-@ type MAValidI MA = {v:Nat | v <  (malen MA)} @-}
{-@ type MAValidO MA = {v:Nat | v <= (malen MA)} @-}

{-@ new :: forall s. n:Nat -> ST s (MArrayN s n) @-}
new          :: forall s. Int -> ST s (MArray s)
new n
  | n < 0 || n .&. highBit /= 0 = error $ "new: size overflow"
  | otherwise = ST $ \s1# ->
       case newByteArray# len# s1# of
         (# s2#, marr# #) -> (# s2#, MArray marr# n #)
  where !(I# len#) = bytesInArray n
        highBit    = maxBound `xor` (maxBound `shiftR` 1)
        bytesInArray n = n `shiftL` 1

{-@ unsafeWrite :: ma:MArray s -> MAValidI ma -> Word16 -> ST s () @-}
unsafeWrite  :: MArray s -> Int -> Word16 -> ST s ()
unsafeWrite MArray{..} i@(I# i#) (W16# e#)
  | i < 0 || i >= maLen = liquidError "out of bounds"
  | otherwise = ST $ \s1# ->
      case writeWord16Array# maBA i# e# s1# of
        s2# -> (# s2#, () #)

{-@ copyM :: dest:MArray s 
          -> didx:MAValidO dest
          -> src:MArray s 
          -> sidx:MAValidO src
          -> {v:Nat | (((didx + v) <= (malen dest))
                    && ((sidx + v) <= (malen src)))}
          -> ST s ()
  @-}
copyM        :: MArray s               -- ^ Destination
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

{-@ memcpyM :: MutableByteArray# s -> CSize -> MutableByteArray# s -> CSize -> CSize -> IO () @-}
memcpyM :: MutableByteArray# s -> CSize -> MutableByteArray# s -> CSize -> CSize -> IO ()
memcpyM = undefined

{-@ unsafeFreeze :: ma:MArray s -> ST s (ArrayN (malen ma)) @-}
unsafeFreeze :: MArray s -> ST s Array
unsafeFreeze MArray{..} = ST $ \s# ->
                          (# s#, Array (unsafeCoerce# maBA) maLen #)

{-@ unsafeIndex :: a:Array -> AValidI a -> Word16 @-}
unsafeIndex  :: Array -> Int -> Word16
unsafeIndex Array{..} i@(I# i#)
  | i < 0 || i >= aLen = liquidError "out of bounds"
  | otherwise = case indexWord16Array# aBA i# of
                  r# -> (W16# r#)

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

{-@ type TValidI T   = {v:Nat | v     <  (tlen T)} @-}
{-@ type TValidO A   = {v:Nat | v     <= (alen A)} @-}
{-@ type TValidL O A = {v:Nat | (v+O) <= (alen A)} @-}


--------------------------------------------------------------------------------
--- From TextRead
--------------------------------------------------------------------------------

{-@ measure numchars :: Array -> Int -> Int -> Int @-}
{-@ measure tlength :: Text -> Int @-}
{-@ invariant {v:Text | (tlength v) = (numchars (tarr v) (toff v) (tlen v))} @-}

--------------------------------------------------------------------------------
--- Helpers
--------------------------------------------------------------------------------

{-@ qualif Ord(v:int, i:int, x:Char)
        : ((((ord x) <  65536) => (v = i))
        && (((ord x) >= 65536) => (v = (i + 1))))
  @-}

\end{code}

</div>

We mentioned previously that `text` uses stream fusion to optimize
multiple loops over a `Text` into a single loop; as a result many of
the top-level API functions are simple wrappers around equivalent
functions over `Stream`s. The creation of `Text` values is then
largely handled by a single function, `unstream`, which converts a
`Stream` into a `Text`.

\begin{code}
unstream :: Stream Char -> Text
unstream (Stream next0 s0 len) = runST $ do
  let mlen = upperBound 4 len
  arr0 <- new mlen
  let outer arr top = loop
       where
        loop !s !i =
            case next0 s of
              Done          -> do
                arr' <- unsafeFreeze arr
                return $! Text arr' 0 i
              Skip s'       -> loop s' i
              Yield x s'
                | j >= top  -> do
                  let top' = (top + 1) `shiftL` 1
                  arr' <- new top'
                  copyM arr' 0 arr 0 top
                  outer arr' top' s i
                | otherwise -> do
                  d <- writeChar arr i x
                  loop s' (i+d)
                where j | ord x < 0x10000 = i
                        | otherwise       = i + 1
  outer arr0 mlen s0 0
\end{code}

Since we're focusing on memory safety here we won't go into detail
about how `Stream`s work. Let's instead jump right into the inner
`loop` and look at the `Yield` case. Here we need to write a char `x`
into `arr`, so we compute the maximal index `j` to which we will
write -- i.e. if `x >= U+10000` then `j = i + 1` -- and determine
whether we can safely write at `j`. If the write is unsafe we have to
allocate a larger array before continuing, otherwise we write `x` and
increment `i` by `x`s width.

Since `writeChar` has to handle writing *any* Unicode value, we need
to assure it that there will always be room to write `x` into `arr`,
regardless of `x`s width. Indeed, this is expressed in the type we
give to `writeChar`.

\begin{code}
{-@ writeChar :: ma:MArray s -> i:Nat -> {v:Char | (Room v ma i)}
              -> ST s {v:Nat | (RoomN v ma i)}
  @-}
\end{code}

The predicate aliases `Room` and `RoomN` express that a character can
fit in the array at index `i` and that there are at least `n` slots
available starting at `i` respectively.

\begin{code}
{-@ predicate Room C MA I = (((One C) => (RoomN 1 MA I))
                          && ((Two C) => (RoomN 2 MA I)))
  @-}
{-@ predicate RoomN N MA I = (I+N <= (malen MA)) @-}
\end{code}

The `One` and `Two` predicates express that a character will be
encoded in one or two 16-bit words, by reasoning about its ordinal
value.

\begin{code}
{-@ predicate One C = ((ord C) <  65536) @-}
{-@ predicate Two C = ((ord C) >= 65536) @-}
\end{code}

As with `numchars`, we leave `ord` abstract, but inform LiquidHaskell
that the `ord` *function* does in fact return the ordinal value of the
character.

\begin{code}
{-@ measure ord :: Char -> Int @-}
{-@ ord :: c:Char -> {v:Int | v = (ord c)} @-}
\end{code}

Since `writeChar` assumes that it will never be called unless there is room to
write `c`, it is safe to just split `c` into 16-bit words and write them into
the array.

\begin{code}
writeChar :: MArray s -> Int -> Char -> ST s Int
writeChar marr i c
    | n < 0x10000 = do
        unsafeWrite marr i (fromIntegral n)
        return 1
    | otherwise = do
        unsafeWrite marr i lo
        unsafeWrite marr (i+1) hi
        return 2
    where n = ord c
          m = n - 0x10000
          lo = fromIntegral $ (m `shiftR` 10) + 0xD800
          hi = fromIntegral $ (m .&. 0x3FF) + 0xDC00
\end{code}

In typical design-by-contract style, we're putting the burden of proof to
establish safety on `writeChar`s caller. Now, scroll back up to
`unstream` and mouse over `j` to see its inferred type.
\begin{code} You should see something like
{v:Int | ((ord x >= 65536) => (v == i+1))
      && ((ord x <  65536) => (v == i))}
\end{code}
which, combined with the case-split on `j >= top`, provides the proof that
writing `x` will be safe!

Stay tuned, next time we'll look at another example of building a `Text` where
LiquidHaskell fails to infer this crucial refinement...
