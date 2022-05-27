{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP, NoImplicitPrelude, BangPatterns, MagicHash #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Bits
-- Copyright   :  (c) The University of Glasgow 2001
-- License     :  BSD-style (see the file libraries/base/LICENSE)
-- 
-- Maintainer  :  libraries@haskell.org
-- Stability   :  experimental
-- Portability :  portable
--
-- This module defines bitwise operations for signed and unsigned
-- integers.  Instances of the class 'Bits' for the 'Int' and
-- 'Integer' types are available from this module, and instances for
-- explicitly sized integral types are available from the
-- "Data.Int" and "Data.Word" modules.
--
-----------------------------------------------------------------------------

module Data.Bits ( 
  Bits(
    (.&.), (.|.), xor, -- :: a -> a -> a
    complement,        -- :: a -> a
    shift,             -- :: a -> Int -> a
    rotate,            -- :: a -> Int -> a
    bit,               -- :: Int -> a
    setBit,            -- :: a -> Int -> a
    clearBit,          -- :: a -> Int -> a
    complementBit,     -- :: a -> Int -> a
    testBit,           -- :: a -> Int -> Bool
    bitSize,           -- :: a -> Int
    isSigned,          -- :: a -> Bool
    shiftL, shiftR,    -- :: a -> Int -> a
    unsafeShiftL, unsafeShiftR,  -- :: a -> Int -> a
    rotateL, rotateR,  -- :: a -> Int -> a
    popCount           -- :: a -> Int
  )

  -- instance Bits Int
  -- instance Bits Integer
 ) where

-- Defines the @Bits@ class containing bit-based operations.
-- See library document for details on the semantics of the
-- individual operations.

#if defined(__GLASGOW_HASKELL__) || defined(__HUGS__)
#include "MachDeps.h"
#endif

#ifdef __GLASGOW_HASKELL__
import GHC.Num
import GHC.Base
#endif

#ifdef __HUGS__
import Hugs.Bits
#endif

infixl 8 `shift`, `rotate`, `shiftL`, `shiftR`, `rotateL`, `rotateR`
infixl 7 .&.
infixl 6 `xor`
infixl 5 .|.

{-| 
The 'Bits' class defines bitwise operations over integral types.

* Bits are numbered from 0 with bit 0 being the least
  significant bit.

Minimal complete definition: '.&.', '.|.', 'xor', 'complement',
('shift' or ('shiftL' and 'shiftR')), ('rotate' or ('rotateL' and 'rotateR')),
'bitSize' and 'isSigned'.
-}
class (Eq a, Num a) => Bits a where
    -- | Bitwise \"and\"
    (.&.) :: a -> a -> a

    -- | Bitwise \"or\"
    (.|.) :: a -> a -> a

    -- | Bitwise \"xor\"
    xor :: a -> a -> a

    {-| Reverse all the bits in the argument -}
    complement        :: a -> a

    {-| @'shift' x i@ shifts @x@ left by @i@ bits if @i@ is positive,
        or right by @-i@ bits otherwise.
        Right shifts perform sign extension on signed number types;
        i.e. they fill the top bits with 1 if the @x@ is negative
        and with 0 otherwise.

        An instance can define either this unified 'shift' or 'shiftL' and
        'shiftR', depending on which is more convenient for the type in
        question. -}
    shift             :: a -> Int -> a

    x `shift`   i | i<0       = x `shiftR` (-i)
                  | i>0       = x `shiftL` i
                  | otherwise = x

    {-| @'rotate' x i@ rotates @x@ left by @i@ bits if @i@ is positive,
        or right by @-i@ bits otherwise.

        For unbounded types like 'Integer', 'rotate' is equivalent to 'shift'.

        An instance can define either this unified 'rotate' or 'rotateL' and
        'rotateR', depending on which is more convenient for the type in
        question. -}
    rotate            :: a -> Int -> a

    x `rotate`  i | i<0       = x `rotateR` (-i)
                  | i>0       = x `rotateL` i
                  | otherwise = x

    {-
    -- Rotation can be implemented in terms of two shifts, but care is
    -- needed for negative values.  This suggested implementation assumes
    -- 2's-complement arithmetic.  It is commented out because it would
    -- require an extra context (Ord a) on the signature of 'rotate'.
    x `rotate`  i | i<0 && isSigned x && x<0
                         = let left = i+bitSize x in
                           ((x `shift` i) .&. complement ((-1) `shift` left))
                           .|. (x `shift` left)
                  | i<0  = (x `shift` i) .|. (x `shift` (i+bitSize x))
                  | i==0 = x
                  | i>0  = (x `shift` i) .|. (x `shift` (i-bitSize x))
    -}

    -- | @bit i@ is a value with the @i@th bit set and all other bits clear
    bit               :: Int -> a

    -- | @x \`setBit\` i@ is the same as @x .|. bit i@
    setBit            :: a -> Int -> a

    -- | @x \`clearBit\` i@ is the same as @x .&. complement (bit i)@
    clearBit          :: a -> Int -> a

    -- | @x \`complementBit\` i@ is the same as @x \`xor\` bit i@
    complementBit     :: a -> Int -> a

    -- | Return 'True' if the @n@th bit of the argument is 1
    testBit           :: a -> Int -> Bool

    {-| Return the number of bits in the type of the argument.  The actual
        value of the argument is ignored.  The function 'bitSize' is
        undefined for types that do not have a fixed bitsize, like 'Integer'.
        -}
    bitSize           :: a -> Int

    {-| Return 'True' if the argument is a signed type.  The actual
        value of the argument is ignored -}
    isSigned          :: a -> Bool

    {-# INLINE bit #-}
    {-# INLINE setBit #-}
    {-# INLINE clearBit #-}
    {-# INLINE complementBit #-}
    {-# INLINE testBit #-}
    bit i               = 1 `shiftL` i
    x `setBit` i        = x .|. bit i
    x `clearBit` i      = x .&. complement (bit i)
    x `complementBit` i = x `xor` bit i
    x `testBit` i       = (x .&. bit i) /= 0

    {-| Shift the argument left by the specified number of bits
        (which must be non-negative).

        An instance can define either this and 'shiftR' or the unified
        'shift', depending on which is more convenient for the type in
        question. -}
    shiftL            :: a -> Int -> a
    {-# INLINE shiftL #-}
    x `shiftL`  i = x `shift`  i

    {-| Shift the argument left by the specified number of bits.  The
        result is undefined for negative shift amounts and shift amounts
        greater or equal to the 'bitSize'.

        Defaults to 'shiftL' unless defined explicitly by an instance. -}
    unsafeShiftL            :: a -> Int -> a
    {-# INLINE unsafeShiftL #-}
    x `unsafeShiftL` i = x `shiftL` i

    {-| Shift the first argument right by the specified number of bits. The
        result is undefined for negative shift amounts and shift amounts
        greater or equal to the 'bitSize'.

        Right shifts perform sign extension on signed number types;
        i.e. they fill the top bits with 1 if the @x@ is negative
        and with 0 otherwise.

        An instance can define either this and 'shiftL' or the unified
        'shift', depending on which is more convenient for the type in
        question. -}
    shiftR            :: a -> Int -> a
    {-# INLINE shiftR #-}
    x `shiftR`  i = x `shift`  (-i)

    {-| Shift the first argument right by the specified number of bits, which
        must be non-negative an smaller than the number of bits in the type.

        Right shifts perform sign extension on signed number types;
        i.e. they fill the top bits with 1 if the @x@ is negative
        and with 0 otherwise.

        Defaults to 'shiftR' unless defined explicitly by an instance. -}
    unsafeShiftR            :: a -> Int -> a
    {-# INLINE unsafeShiftR #-}
    x `unsafeShiftR` i = x `shiftR` i

    {-| Rotate the argument left by the specified number of bits
        (which must be non-negative).

        An instance can define either this and 'rotateR' or the unified
        'rotate', depending on which is more convenient for the type in
        question. -}
    rotateL           :: a -> Int -> a
    {-# INLINE rotateL #-}
    x `rotateL` i = x `rotate` i

    {-| Rotate the argument right by the specified number of bits
        (which must be non-negative).

        An instance can define either this and 'rotateL' or the unified
        'rotate', depending on which is more convenient for the type in
        question. -}
    rotateR           :: a -> Int -> a
    {-# INLINE rotateR #-}
    x `rotateR` i = x `rotate` (-i)

    {-| Return the number of set bits in the argument.  This number is
        known as the population count or the Hamming weight. -}
    popCount          :: a -> Int
    popCount = go 0
      where
        go !c 0 = c
        go c w = go (c+1) (w .&. (w - 1))  -- clear the least significant bit set
    {-# INLINABLE popCount #-}
    {- This implementation is intentionally naive.  Instances are
       expected to override it with something optimized for their
       size. -}

instance Bits Int where
    {-# INLINE shift #-}

#ifdef __GLASGOW_HASKELL__
    (I# x#) .&.   (I# y#)  = I# (word2Int# (int2Word# x# `and#` int2Word# y#))

    (I# x#) .|.   (I# y#)  = I# (word2Int# (int2Word# x# `or#`  int2Word# y#))

    (I# x#) `xor` (I# y#)  = I# (word2Int# (int2Word# x# `xor#` int2Word# y#))

    complement (I# x#)     = I# (word2Int# (int2Word# x# `xor#` int2Word# (-1#)))

    (I# x#) `shift` (I# i#)
        | i# >=# 0#        = I# (x# `iShiftL#` i#)
        | otherwise        = I# (x# `iShiftRA#` negateInt# i#)
    (I# x#) `shiftL` (I# i#) = I# (x# `iShiftL#` i#)
    (I# x#) `unsafeShiftL` (I# i#) = I# (x# `uncheckedIShiftL#` i#)
    (I# x#) `shiftR` (I# i#) = I# (x# `iShiftRA#` i#)
    (I# x#) `unsafeShiftR` (I# i#) = I# (x# `uncheckedIShiftRA#` i#)

    {-# INLINE rotate #-} 	-- See Note [Constant folding for rotate]
    (I# x#) `rotate` (I# i#) =
        I# (word2Int# ((x'# `uncheckedShiftL#` i'#) `or#`
                       (x'# `uncheckedShiftRL#` (wsib -# i'#))))
      where
        !x'# = int2Word# x#
        !i'# = word2Int# (int2Word# i# `and#` int2Word# (wsib -# 1#))
        !wsib = WORD_SIZE_IN_BITS#   {- work around preprocessor problem (??) -}
    bitSize  _             = WORD_SIZE_IN_BITS

    popCount (I# x#) = I# (word2Int# (popCnt# (int2Word# x#)))

#else /* !__GLASGOW_HASKELL__ */

#ifdef __HUGS__
    (.&.)                  = primAndInt
    (.|.)                  = primOrInt
    xor                    = primXorInt
    complement             = primComplementInt
    shift                  = primShiftInt
    bit                    = primBitInt
    testBit                = primTestInt
    bitSize _              = SIZEOF_HSINT*8
#elif defined(__NHC__)
    (.&.)                  = nhc_primIntAnd
    (.|.)                  = nhc_primIntOr
    xor                    = nhc_primIntXor
    complement             = nhc_primIntCompl
    shiftL                 = nhc_primIntLsh
    shiftR                 = nhc_primIntRsh
    bitSize _              = 32
#endif /* __NHC__ */

    x `rotate`  i
        | i<0 && x<0       = let left = i+bitSize x in
                             ((x `shift` i) .&. complement ((-1) `shift` left))
                             .|. (x `shift` left)
        | i<0              = (x `shift` i) .|. (x `shift` (i+bitSize x))
        | i==0             = x
        | i>0              = (x `shift` i) .|. (x `shift` (i-bitSize x))

#endif /* !__GLASGOW_HASKELL__ */

    isSigned _             = True

#ifdef __NHC__
foreign import ccall nhc_primIntAnd :: Int -> Int -> Int
foreign import ccall nhc_primIntOr  :: Int -> Int -> Int
foreign import ccall nhc_primIntXor :: Int -> Int -> Int
foreign import ccall nhc_primIntLsh :: Int -> Int -> Int
foreign import ccall nhc_primIntRsh :: Int -> Int -> Int
foreign import ccall nhc_primIntCompl :: Int -> Int
#endif /* __NHC__ */

instance Bits Integer where
#if defined(__GLASGOW_HASKELL__)
   (.&.) = andInteger
   (.|.) = orInteger
   xor = xorInteger
   complement = complementInteger
   shift x i@(I# i#) | i >= 0    = shiftLInteger x i#
                     | otherwise = shiftRInteger x (negateInt# i#)
#else
   -- reduce bitwise binary operations to special cases we can handle

   x .&. y   | x<0 && y<0 = complement (complement x `posOr` complement y)
             | otherwise  = x `posAnd` y
   
   x .|. y   | x<0 || y<0 = complement (complement x `posAnd` complement y)
             | otherwise  = x `posOr` y
   
   x `xor` y | x<0 && y<0 = complement x `posXOr` complement y
             | x<0        = complement (complement x `posXOr` y)
             |        y<0 = complement (x `posXOr` complement y)
             | otherwise  = x `posXOr` y

   -- assuming infinite 2's-complement arithmetic
   complement a = -1 - a
   shift x i | i >= 0    = x * 2^i
             | otherwise = x `div` 2^(-i)
#endif

   rotate x i = shift x i   -- since an Integer never wraps around

   bitSize _  = error "Data.Bits.bitSize(Integer)"
   isSigned _ = True

#if !defined(__GLASGOW_HASKELL__)
-- Crude implementation of bitwise operations on Integers: convert them
-- to finite lists of Ints (least significant first), zip and convert
-- back again.

-- posAnd requires at least one argument non-negative
-- posOr and posXOr require both arguments non-negative

posAnd, posOr, posXOr :: Integer -> Integer -> Integer
posAnd x y   = fromInts $ zipWith (.&.) (toInts x) (toInts y)
posOr x y    = fromInts $ longZipWith (.|.) (toInts x) (toInts y)
posXOr x y   = fromInts $ longZipWith xor (toInts x) (toInts y)

longZipWith :: (a -> a -> a) -> [a] -> [a] -> [a]
longZipWith f xs [] = xs
longZipWith f [] ys = ys
longZipWith f (x:xs) (y:ys) = f x y:longZipWith f xs ys

toInts :: Integer -> [Int]
toInts n
    | n == 0 = []
    | otherwise = mkInt (n `mod` numInts):toInts (n `div` numInts)
  where mkInt n | n > toInteger(maxBound::Int) = fromInteger (n-numInts)
                | otherwise = fromInteger n

fromInts :: [Int] -> Integer
fromInts = foldr catInt 0
    where catInt d n = (if d<0 then n+1 else n)*numInts + toInteger d

numInts = toInteger (maxBound::Int) - toInteger (minBound::Int) + 1
#endif /* !__GLASGOW_HASKELL__ */

{- 	Note [Constant folding for rotate]
	~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The INLINE on the Int instance of rotate enables it to be constant
folded.  For example:
     sumU . mapU (`rotate` 3) . replicateU 10000000 $ (7 :: Int)
goes to:
   Main.$wfold =
     \ (ww_sO7 :: Int#) (ww1_sOb :: Int#) ->
       case ww1_sOb of wild_XM {
         __DEFAULT -> Main.$wfold (+# ww_sO7 56) (+# wild_XM 1);
         10000000 -> ww_sO7
whereas before it was left as a call to $wrotate.

All other Bits instances seem to inline well enough on their
own to enable constant folding; for example 'shift':
     sumU . mapU (`shift` 3) . replicateU 10000000 $ (7 :: Int)
 goes to:
     Main.$wfold =
       \ (ww_sOb :: Int#) (ww1_sOf :: Int#) ->
         case ww1_sOf of wild_XM {
           __DEFAULT -> Main.$wfold (+# ww_sOb 56) (+# wild_XM 1);
           10000000 -> ww_sOb
         }
-} 

