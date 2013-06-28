{-# LANGUAGE BangPatterns, CPP, MagicHash, UnboxedTuples #-}

-- Module:      Data.Text.Lazy.Builder.Int
-- Copyright:   (c) 2011 MailRank, Inc.
-- License:     BSD3
-- Maintainer:  Bryan O'Sullivan <bos@serpentine.com>
-- Stability:   experimental
-- Portability: portable
--
-- Efficiently write an integral value to a 'Builder'.

module Data.Text.Lazy.Builder.Int
    (
      decimal
    , hexadecimal
    ) where

import Data.Int (Int8, Int16, Int32, Int64)
import Data.Monoid (mempty)
import Data.Text.Lazy.Builder.Functions ((<>), i2d)
import Data.Text.Lazy.Builder
import Data.Word (Word, Word8, Word16, Word32, Word64)
import GHC.Base (quotInt, remInt)
import GHC.Num (quotRemInteger)
import GHC.Types (Int(..))

#ifdef  __GLASGOW_HASKELL__
# if __GLASGOW_HASKELL__ < 611
import GHC.Integer.Internals
# elif defined(INTEGER_GMP)
import GHC.Integer.GMP.Internals
# elif defined(INTEGER_SIMPLE)
import GHC.Integer
# else
# error "You need to use either GMP or integer-simple."
# endif
#endif

#if defined(INTEGER_GMP) || defined(INTEGER_SIMPLE)
# define PAIR(a,b) (# a,b #)
#else
# define PAIR(a,b) (a,b)
#endif

decimal :: Integral a => a -> Builder
{-# SPECIALIZE decimal :: Int8 -> Builder #-}
{-# RULES "decimal/Int" decimal = boundedDecimal :: Int -> Builder #-}
{-# RULES "decimal/Int16" decimal = boundedDecimal :: Int16 -> Builder #-}
{-# RULES "decimal/Int32" decimal = boundedDecimal :: Int32 -> Builder #-}
{-# RULES "decimal/Int64" decimal = boundedDecimal :: Int64 -> Builder #-}
{-# RULES "decimal/Word" decimal = positive :: Word -> Builder #-}
{-# RULES "decimal/Word8" decimal = positive :: Word8 -> Builder #-}
{-# RULES "decimal/Word16" decimal = positive :: Word16 -> Builder #-}
{-# RULES "decimal/Word32" decimal = positive :: Word32 -> Builder #-}
{-# RULES "decimal/Word64" decimal = positive :: Word64 -> Builder #-}
{-# RULES "decimal/Integer" decimal = integer 10 :: Integer -> Builder #-}
decimal i
  | i < 0     = singleton '-' <>
                if i <= -128
                then positive (-(i `quot` 10)) <> digit (-(i `rem` 10))
                else positive (-i)
  | otherwise = positive i

boundedDecimal :: (Integral a, Bounded a) => a -> Builder
{-# SPECIALIZE boundedDecimal :: Int -> Builder #-}
{-# SPECIALIZE boundedDecimal :: Int8 -> Builder #-}
{-# SPECIALIZE boundedDecimal :: Int16 -> Builder #-}
{-# SPECIALIZE boundedDecimal :: Int32 -> Builder #-}
{-# SPECIALIZE boundedDecimal :: Int64 -> Builder #-}
boundedDecimal i
    | i < 0     = singleton '-' <>
                  if i == minBound
                  then positive (-(i `quot` 10)) <> digit (-(i `rem` 10))
                  else positive (-i)
    | otherwise = positive i

positive :: (Integral a) => a -> Builder
{-# SPECIALIZE positive :: Int -> Builder #-}
{-# SPECIALIZE positive :: Int8 -> Builder #-}
{-# SPECIALIZE positive :: Int16 -> Builder #-}
{-# SPECIALIZE positive :: Int32 -> Builder #-}
{-# SPECIALIZE positive :: Int64 -> Builder #-}
{-# SPECIALIZE positive :: Word -> Builder #-}
{-# SPECIALIZE positive :: Word8 -> Builder #-}
{-# SPECIALIZE positive :: Word16 -> Builder #-}
{-# SPECIALIZE positive :: Word32 -> Builder #-}
{-# SPECIALIZE positive :: Word64 -> Builder #-}
positive = go
  where go n | n < 10    = digit n
             | otherwise = go (n `quot` 10) <> digit (n `rem` 10)

hexadecimal :: Integral a => a -> Builder
{-# SPECIALIZE hexadecimal :: Int -> Builder #-}
{-# SPECIALIZE hexadecimal :: Int8 -> Builder #-}
{-# SPECIALIZE hexadecimal :: Int16 -> Builder #-}
{-# SPECIALIZE hexadecimal :: Int32 -> Builder #-}
{-# SPECIALIZE hexadecimal :: Int64 -> Builder #-}
{-# SPECIALIZE hexadecimal :: Word -> Builder #-}
{-# SPECIALIZE hexadecimal :: Word8 -> Builder #-}
{-# SPECIALIZE hexadecimal :: Word16 -> Builder #-}
{-# SPECIALIZE hexadecimal :: Word32 -> Builder #-}
{-# SPECIALIZE hexadecimal :: Word64 -> Builder #-}
{-# RULES "hexadecimal/Integer" hexadecimal = integer 16 :: Integer -> Builder #-}
hexadecimal i
    | i < 0     = error msg
    | otherwise = go i
  where
    go n | n < 16    = hexDigit n
         | otherwise = go (n `quot` 16) <> hexDigit (n `rem` 16)
    msg = "Data.Text.Lazy.Builder.Int.hexadecimal: applied to negative number"

digit :: Integral a => a -> Builder
digit n = singleton $! i2d (fromIntegral n)
{-# INLINE digit #-}

hexDigit :: Integral a => a -> Builder
hexDigit n
    | n <= 9    = singleton $! i2d (fromIntegral n)
    | otherwise = singleton $! toEnum (fromIntegral n + 87)
{-# INLINE hexDigit #-}

int :: Int -> Builder
int = decimal
{-# INLINE int #-}

data T = T !Integer !Int

integer :: Int -> Integer -> Builder
#ifdef INTEGER_GMP
integer 10 (S# i#) = decimal (I# i#)
integer 16 (S# i#) = hexadecimal (I# i#)
#else
integer 10 i = decimal i
integer 16 i = hexadecimal i
#endif
integer base i
    | i < 0     = singleton '-' <> go (-i)
    | otherwise = go i
  where
    go n | n < maxInt = int (fromInteger n)
         | otherwise  = putH (splitf (maxInt * maxInt) n)

    splitf p n
      | p > n       = [n]
      | otherwise   = splith p (splitf (p*p) n)

    splith p (n:ns) = case n `quotRemInteger` p of
                        PAIR(q,r) | q > 0     -> q : r : splitb p ns
                                  | otherwise -> r : splitb p ns
    splith _ _      = error "splith: the impossible happened."

    splitb p (n:ns) = case n `quotRemInteger` p of
                        PAIR(q,r) -> q : r : splitb p ns
    splitb _ _      = []

    T maxInt10 maxDigits10 =
        until ((>mi) . (*10) . fstT) (\(T n d) -> T (n*10) (d+1)) (T 10 1)
      where mi = fromIntegral (maxBound :: Int)
    T maxInt16 maxDigits16 =
        until ((>mi) . (*16) . fstT) (\(T n d) -> T (n*16) (d+1)) (T 16 1)
      where mi = fromIntegral (maxBound :: Int)

    fstT (T a _) = a

    maxInt | base == 10 = maxInt10
           | otherwise  = maxInt16
    maxDigits | base == 10 = maxDigits10
              | otherwise  = maxDigits16

    putH (n:ns) = case n `quotRemInteger` maxInt of
                    PAIR(x,y)
                        | q > 0     -> int q <> pblock r <> putB ns
                        | otherwise -> int r <> putB ns
                        where q = fromInteger x
                              r = fromInteger y
    putH _ = error "putH: the impossible happened"

    putB (n:ns) = case n `quotRemInteger` maxInt of
                    PAIR(x,y) -> pblock q <> pblock r <> putB ns
                        where q = fromInteger x
                              r = fromInteger y
    putB _ = mempty

    pblock = loop maxDigits
      where
        loop !d !n
            | d == 1    = digit n
            | otherwise = loop (d-1) q <> digit r
            where q = n `quotInt` base
                  r = n `remInt` base
