{-# LANGUAGE CPP, MagicHash #-}

-- |
-- Module      : Data.Text.UnsafeChar
-- Copyright   : (c) 2008, 2009 Tom Harper,
--               (c) 2009, 2010 Bryan O'Sullivan,
--               (c) 2009 Duncan Coutts
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : GHC
--
-- Fast character manipulation functions.
module Data.Text.UnsafeChar
    (
      ord
    , unsafeChr
    , unsafeChr8
    , unsafeChr32
    , unsafeWrite
    -- , unsafeWriteRev
    ) where

#ifdef ASSERTS
import Control.Exception (assert)
#endif
import Control.Monad.ST (ST)
import Data.Bits ((.&.))
import Data.Text.UnsafeShift (shiftR)
import GHC.Exts (Char(..), Int(..), chr#, ord#, word2Int#)
import GHC.Word (Word8(..), Word16(..), Word32(..))
import qualified Data.Text.Array as A

--LIQUID
import Language.Haskell.Liquid.Prelude

{-@ measure ord :: Char -> Int @-}
{-@ predicate One C = ((ord C) <  65536) @-}
{-@ predicate Two C = ((ord C) >= 65536) @-}

{-@ qualOneC :: {v:Char | (ord v) <  65536} -> () @-}
qualOneC :: Char -> ()
qualOneC _ = ()
{-@ qualTwoC :: {v:Char | (ord v) >= 65536} -> () @-}
qualTwoC :: Char -> ()
qualTwoC _ = ()

{-@ predicate Room MA I C = (((One C) => (MAValidIN MA I 1))
                          && ((Two C) => (MAValidIN MA I 2))) @-}
{-@ predicate MAValidIN  MA I N = (BtwnI I 0 ((malen MA) - N)) @-}

{- predicate RoomFront MA I N = (BtwnI I N (malen MA)) @-}

{-@ ord :: c:Char -> {v:Int | v = (ord c)} @-}
ord :: Char -> Int
ord c@(C# c#) = let i = I# (ord# c#)
                in liquidAssume (axiom_ord c i) i
{-@ axiom_ord :: c:Char -> i:Int -> {v:Bool | ((Prop v) <=> (i = (ord c)))} @-}
axiom_ord :: Char -> Int -> Bool
axiom_ord = undefined
{-# INLINE ord #-}

unsafeChr :: Word16 -> Char
unsafeChr (W16# w#) = C# (chr# (word2Int# w#))
{-# INLINE unsafeChr #-}

unsafeChr8 :: Word8 -> Char
unsafeChr8 (W8# w#) = C# (chr# (word2Int# w#))
{-# INLINE unsafeChr8 #-}

unsafeChr32 :: Word32 -> Char
unsafeChr32 (W32# w#) = C# (chr# (word2Int# w#))
{-# INLINE unsafeChr32 #-}

-- | Write a character into the array at the given offset.  Returns
-- the number of 'Word16's written.
{-@ unsafeWrite :: ma:A.MArray s -> i:Nat -> {v:Char | (Room ma i v)}
                -> ST s {v:(MAValidL i ma) | (BtwnI v 1 2)}
  @-}
unsafeWrite :: A.MArray s -> Int -> Char -> ST s Int
unsafeWrite marr i c
    | n < 0x10000 = do
-- #if defined(ASSERTS)
        liquidAssert (i >= 0) . liquidAssert (i < A.maLen marr) $ return ()
-- #endif
        A.unsafeWrite marr i (fromIntegral n)
        return 1
    | otherwise = do
-- #if defined(ASSERTS)
        liquidAssert (i >= 0) . liquidAssert (i < A.maLen marr - 1) $ return ()
-- #endif
        A.unsafeWrite marr i lo
        A.unsafeWrite marr (i+1) hi
        return 2
    where n = ord c
          m = n - 0x10000
          lo = fromIntegral $ (m `shiftR` 10) + 0xD800
          hi = fromIntegral $ (m .&. 0x3FF) + 0xDC00
{-# INLINE unsafeWrite #-}

{-
unsafeWriteRev :: A.MArray s Word16 -> Int -> Char -> ST s Int
unsafeWriteRev marr i c
    | n < 0x10000 = do
        assert (i >= 0) . assert (i < A.length marr) $
          A.unsafeWrite marr i (fromIntegral n)
        return (i-1)
    | otherwise = do
        assert (i >= 1) . assert (i < A.length marr) $
          A.unsafeWrite marr (i-1) lo
        A.unsafeWrite marr i hi
        return (i-2)
    where n = ord c
          m = n - 0x10000
          lo = fromIntegral $ (m `shiftR` 10) + 0xD800
          hi = fromIntegral $ (m .&. 0x3FF) + 0xDC00
{-# INLINE unsafeWriteRev #-}
-}
