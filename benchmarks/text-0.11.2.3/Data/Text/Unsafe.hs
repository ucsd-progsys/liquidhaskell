{-# LANGUAGE CPP, MagicHash, UnboxedTuples #-}
-- |
-- Module      : Data.Text.Unsafe
-- Copyright   : (c) 2009, 2010, 2011 Bryan O'Sullivan
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : portable
--
-- A module containing unsafe 'Text' operations, for very very careful
-- use in heavily tested code.
module Data.Text.Unsafe
    (
      inlineInterleaveST
    , inlinePerformIO
    , Iter(..)
    , iter
    , iter_
    , reverseIter
    , unsafeHead
    , unsafeTail
    , lengthWord16
    , takeWord16
    , dropWord16
    ) where

#if defined(ASSERTS)
import Control.Exception (assert)
#endif
import Data.Text.Encoding.Utf16 (chr2)
import Data.Text.Internal (Text(..))
import Data.Text.Unsafe.Base (inlineInterleaveST, inlinePerformIO)
import Data.Text.UnsafeChar (unsafeChr)
import qualified Data.Text.Array as A

--LIQUID
import Data.Text.Axioms
import Language.Haskell.Liquid.Prelude

-- | /O(1)/ A variant of 'head' for non-empty 'Text'. 'unsafeHead'
-- omits the check for the empty case, so there is an obligation on
-- the programmer to provide a proof that the 'Text' is non-empty.
{-@ unsafeHead :: TextNE -> Char @-}
unsafeHead :: Text -> Char
unsafeHead (Text arr off _len)
    | m < 0xD800 || m > 0xDBFF = unsafeChr m
    | otherwise                = chr2 m n
    where m = A.unsafeIndexF arr off _len off
          {-@ LAZYVAR n @-}
          n = A.unsafeIndex arr (off+1)
{-# INLINE unsafeHead #-}

-- | /O(1)/ A variant of 'tail' for non-empty 'Text'. 'unsafeHead'
-- omits the check for the empty case, so there is an obligation on
-- the programmer to provide a proof that the 'Text' is non-empty.
{-@ unsafeTail :: t:TextNE -> {v:TextLT t | (tlength v) = ((tlength t) - 1)} @-}
unsafeTail :: Text -> Text
unsafeTail t@(Text arr off len) =
--LIQUID #if defined(ASSERTS)
--LIQUID     assert (d <= len) $
--LIQUID #endif
    liquidAssert (d <= len) $
    Text arr (off+d) len'
  where d = iter_ t 0
        len' = liquidAssume (axiom_numchars_split t d) (len-d)
{-# INLINE unsafeTail #-}

data Iter = Iter {-# UNPACK #-} !Char {-# UNPACK #-} !Int

{-@ measure iter_d :: Iter -> Int
    iter_d (Iter c d) = d
  @-}

{-@ qualif IterD(v:Int, i:Iter) : v = (iter_d i) @-}
{-@ qualif ReverseIter(v:Int, i:Int, t:Text)
        : ((((i+1)+v) >= 0) && (((i+1)+v) < (i+1))
           && ((numchars (tarr t) (toff t) ((i+1)+v))
               = ((numchars (tarr t) (toff t) (i+1)) - 1))
           && ((numchars (tarr t) (toff t) ((i+1)+v)) >= -1))
  @-}


-- | /O(1)/ Iterate (unsafely) one step forwards through a UTF-16
-- array, returning the current character and the delta to add to give
-- the next offset to iterate at.
{-@ iter :: t:Text
         -> i:{v:Nat | v < (tlen t)}
         -> {v:Iter | ((BtwnEI ((iter_d v)+i) i (tlen t))
                && ((numchars (tarr t) (toff t) (i+(iter_d v)))
                    = (1 + (numchars (tarr t) (toff t) i)))
                && ((numchars (tarr t) (toff t) (i+(iter_d v)))
                    <= (tlength t)))}
  @-}
iter :: Text -> Int -> Iter
iter (Text arr off _len) i
    | m < 0xD800 || m > 0xDBFF = Iter (unsafeChr m) 1
    | otherwise                = let k = j + 1
                                     n = A.unsafeIndex arr k
                                 in
                                 Iter (chr2 m n) 2
  where m = A.unsafeIndexF arr off _len j
        j = off + i
        {- LAZYVAR n @-}
        -- n = A.unsafeIndex arr k
        {- LAZYVAR k @-}
        -- k = j + 1
{-# INLINE iter #-}

-- | /O(1)/ Iterate one step through a UTF-16 array, returning the
-- delta to add to give the next offset to iterate at.
{-@ iter_ :: t:Text
          -> i:{v:Nat | v < (tlen t)}
          -> {v:Int | (((BtwnEI (v+i) i (tlen t)))
                       && ((numchars (tarr t) (toff t) (i+v))
                           = (1 + (numchars (tarr t) (toff t) i)))
                       && ((numchars (tarr t) (toff t) (i+v))
                           <= (tlength t)))}
  @-}
iter_ :: Text -> Int -> Int
iter_ (Text arr off _len) i | m < 0xD800 || m > 0xDBFF = 1
                            | otherwise                = 2
--LIQUID   where m = A.unsafeIndex arr (off+i)
  where m = A.unsafeIndexF arr off _len (off+i)
{-# INLINE iter_ #-}

-- | /O(1)/ Iterate one step backwards through a UTF-16 array,
-- returning the current character and the delta to add (i.e. a
-- negative number) to give the next offset to iterate at.
{-@ reverseIter :: t:Text
                -> i:{v:Int | (Btwn v 0 (tlen t))}
                -> (Char,{v:Int | ((Btwn ((i+1)+v) 0 (i+1))
                          && ((numchars (tarr t) (toff t) ((i+1)+v))
                              = ((numchars (tarr t) (toff t) (i+1)) - 1))
                          && ((numchars (tarr t) (toff t) ((i+1)+v)) >= -1))})
  @-}
--LIQUID reverseIter :: Text -> Int -> (Char,Int)
--LIQUID reverseIter (Text arr off _len) i
reverseIter :: Text -> Int -> (Char,Int)
reverseIter (Text arr off _len) i
    | m < 0xDC00 || m > 0xDFFF = (unsafeChr m, neg 1)
    | otherwise                = let k = j - 1
                                     n = A.unsafeIndex arr k
                                 in
                                  (chr2 n m,    neg 2)
  where m = A.unsafeIndexB arr off _len j
        {- LAZYVAR n @-}
        -- n = A.unsafeIndex arr k
        j = off + i
        {- LAZYVAR k @-}
        -- k = j - 1
{-# INLINE reverseIter #-}

{-@ neg :: n:Int -> {v:Int | v = (0-n)} @-}
neg :: Int -> Int
neg n = 0-n


-- | /O(1)/ Return the length of a 'Text' in units of 'Word16'.  This
-- is useful for sizing a target array appropriately before using
-- 'unsafeCopyToPtr'.
{-@ lengthWord16 :: t:Text -> {v:Int | v = (tlen t)} @-}
lengthWord16 :: Text -> Int
lengthWord16 (Text _arr _off len) = len
{-# INLINE lengthWord16 #-}

-- | /O(1)/ Unchecked take of 'k' 'Word16's from the front of a 'Text'.
{-@ takeWord16 :: k:Nat -> {v:Text | (k <= (tlen v))} -> {v:Text | (tlen v) = k} @-}
takeWord16 :: Int -> Text -> Text
takeWord16 k (Text arr off _len) = Text arr off k
{-# INLINE takeWord16 #-}

-- | /O(1)/ Unchecked drop of 'k' 'Word16's from the front of a 'Text'.
{-@ dropWord16 :: k:Nat -> t:{v:Text | (k <= (tlen v))}
               -> {v:Text | (tlen v) = ((tlen t) - k)} @-}
dropWord16 :: Int -> Text -> Text
dropWord16 k (Text arr off len) = Text arr (off+k) (len-k)
{-# INLINE dropWord16 #-}
