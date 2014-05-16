---
layout: post
title: "Text Bug"
date: 2014-03-01
comments: true
external-url:
author: Eric Seidel
published: false
categories: benchmarks, text
demo: TextBug.hs
---

For our last post on `text`, we return to the topic of building a new `Text`
value, i.e. proving the safety of write operations.

<!-- more -->

<div class="hidden">

\begin{code}
{-# LANGUAGE BangPatterns, CPP, MagicHash, Rank2Types,
    RecordWildCards, UnboxedTuples, ExistentialQuantification #-}
{-@ LIQUID "--no-termination" @-}
module TextBug where

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
  | n < 0 || n .&. highBit /= 0 = error $ "Data.Text.Array.new: size overflow"
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
{-@ data Text [tlen] = Text (tarr :: Array)
                            (toff :: TValidO tarr)
                            (tlen :: TValidL toff tarr)
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
--- From TextWrite
--------------------------------------------------------------------------------

{-@ qualif Ord(v:int, i:int, x:Char)
        : ((((ord x) <  65536) => (v = i))
        && (((ord x) >= 65536) => (v = (i + 1))))
  @-}

{-@ predicate Room C MA I = (((One C) => (RoomN 1 MA I))
                          && ((Two C) => (RoomN 2 MA I)))
  @-}
{-@ predicate RoomN N MA I = (I+N <= (malen MA)) @-}

{-@ measure ord :: Char -> Int @-}
{-@ ord :: c:Char -> {v:Int | v = (ord c)} @-}
{-@ predicate One C = ((ord C) <  65536) @-}
{-@ predicate Two C = ((ord C) >= 65536) @-}

{-@ writeChar :: ma:MArray s -> i:Nat -> {v:Char | (Room v ma i)}
              -> ST s {v:Nat | (RoomN v ma i)}
  @-}
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

--------------------------------------------------------------------------------
--- Helpers
--------------------------------------------------------------------------------

{-@ qualif MALenLE(v:int, a:MArray s): v <= (malen a) @-}
{-@ qualif ALenLE(v:int, a:Array): v <= (alen a) @-}

\end{code}

</div>

Let's take a look at `mapAccumL`, which combines a map and a fold
over a `Stream` and bundles the result of the map into a new `Text`.
Again, we'll want to focus our attention on the `Yield` case of the
inner loop.

\begin{code}
mapAccumL f z0 (Stream next0 s0 len) =
  (nz, Text na 0 nl)
 where
  mlen = upperBound 4 len
  (na,(nz,nl)) = runST $ do
       (marr,x) <- (new mlen >>= \arr ->
                    outer arr mlen z0 s0 0)
       arr      <- unsafeFreeze marr
       return (arr,x)
  outer arr top = loop
   where
    loop !z !s !i =
      case next0 s of
        Done          -> return (arr, (z,i))
        Skip s'       -> loop z s' i
        Yield x s'
          | j >= top  -> do
            let top' = (top + 1) `shiftL` 1
            arr' <- new top'
            copyM arr' 0 arr 0 top
            outer arr' top' z s i
          | otherwise -> do
            let (z',c) = f z x
            d <- writeChar arr i c
            loop z' s' (i+d)
          where j | ord x < 0x10000 = i
                  | otherwise       = i + 1
\end{code}

If you recall `unstream` from last time, you'll notice that this loop body
looks almost identical to the one found in `unstream`, but LiquidHaskell has
flagged the `writeChar` call as unsafe! What's going on here?

Let's take a look at `j`, recalling that it carried a crucial part of the safety
\begin{code} proof last time, and see what LiquidHaskell was able to infer.
{v:Int | ((ord x >= 65536) => (v == i+1))
      && ((ord x <  65536) => (v == i))}
\end{code}

Well that's not very useful at all! LiquidHaskell can prove that it's safe to
write `x` but here we are trying to write `c` into the array. This is actually
a *good* thing though, because `c` is the result of calling an arbitrary
function `f` on `x`! We haven't constrained `f` in any way, so it could easily
return a character above `U+10000` given any input.

So `mapAccumL` is actually *unsafe*, and our first wild bug caught by
LiquidHaskell! The fix is luckily easy, we simply have to lift the
`let (z',c) = f z x` binder into the `where` clause, and change `j` to
depend on `ord c` instead.

\begin{code}
mapAccumL' f z0 (Stream next0 s0 len) =
  (nz, Text na 0 nl)
 where
  mlen = upperBound 4 len
  (na,(nz,nl)) = runST $ do
       (marr,x) <- (new mlen >>= \arr ->
                    outer arr mlen z0 s0 0)
       arr      <- unsafeFreeze marr
       return (arr,x)
  outer arr top = loop
   where
    loop !z !s !i =
      case next0 s of
        Done          -> return (arr, (z,i))
        Skip s'       -> loop z s' i
        Yield x s'
          | j >= top  -> do
            let top' = (top + 1) `shiftL` 1
            arr' <- new top'
            copyM arr' 0 arr 0 top
            outer arr' top' z s i
          | otherwise -> do
            d <- writeChar arr i c
            loop z' s' (i+d)
          where (z',c) = f z x
                j | ord c < 0x10000 = i
                  | otherwise       = i + 1
\end{code}

LiquidHaskell happily accepts our revised `mapAccumL`, as did the `text`
maintainers.

We hope you've enjoyed this whirlwind tour of using LiquidHaskell to verify
production code, we have many more examples in the `benchmarks` folder of
our GitHub repository for the intrepid reader.
