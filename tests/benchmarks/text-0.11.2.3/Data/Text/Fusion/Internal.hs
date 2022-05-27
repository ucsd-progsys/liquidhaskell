{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--bscope" @-}
{-@ LIQUID "--no-check-imports"@-}
{-@ LIQUID "--no-totality"    @-}

{-# LANGUAGE BangPatterns, ExistentialQuantification #-}
-- |
-- Module      : Data.Text.Fusion.Internal
-- Copyright   : (c) Tom Harper 2008-2009,
--               (c) Bryan O'Sullivan 2009,
--               (c) Duncan Coutts 2009,
--               (c) Jasper Van der Jeugt 2011
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : GHC
--
-- Core stream fusion functionality for text.

module Data.Text.Fusion.Internal
    (
      CC(..)
    , M(..)
    , M8
    , PairS(..)
    , RS(..)
    , Step(..)
    , Stream(..)
    , Switch(..)
    , empty
    ) where

import Data.Text.Fusion.Size
import Data.Word (Word8)

-- | Specialised tuple for case conversion.
data CC s = CC !s {-# UNPACK #-} !Char {-# UNPACK #-} !Char

-- | Specialised, strict Maybe-like type.
data M a = N
         | J !a

type M8 = M Word8

-- Restreaming state.
data RS s
    = RS0 !s
    | RS1 !s {-# UNPACK #-} !Word8
    | RS2 !s {-# UNPACK #-} !Word8 {-# UNPACK #-} !Word8
    | RS3 !s {-# UNPACK #-} !Word8 {-# UNPACK #-} !Word8 {-# UNPACK #-} !Word8

infixl 2 :*:
data PairS a b = !a :*: !b
                 -- deriving (Eq, Ord, Show)

-- | Allow a function over a stream to switch between two states.
data Switch = S1 | S2

data Step s a = Done
              | Skip !s
              | Yield !a !s

{-
instance (Show a) => Show (Step s a)
    where show Done        = "Done"
          show (Skip _)    = "Skip"
          show (Yield x _) = "Yield " ++ show x
-}

instance (Eq a) => Eq (Stream a) where
    (==) = eq

instance (Ord a) => Ord (Stream a) where
    compare = cmp

-- The length hint in a Stream has two roles.  If its value is zero,
-- we trust it, and treat the stream as empty.  Otherwise, we treat it
-- as a hint: it should usually be accurate, so we use it when
-- unstreaming to decide what size array to allocate.  However, the
-- unstreaming functions must be able to cope with the hint being too
-- small or too large.
--
-- The size hint tries to track the UTF-16 code points in a stream,
-- but often counts the number of characters instead.  It can easily
-- undercount if, for instance, a transformed stream contains astral
-- plane characters (those above 0x10000).

data Stream a =
    forall s. Stream
    (s -> Step s a)             -- stepper function
    !s                          -- current state
    !Size                       -- size hint

-- | /O(n)/ Determines if two streams are equal.
eq :: (Eq a) => Stream a -> Stream a -> Bool
eq (Stream next1 s1 _) (Stream next2 s2 _) = loop (next1 s1) (next2 s2)
    where
      loop Done Done                     = True
      loop (Skip s1')     (Skip s2')     = loop (next1 s1') (next2 s2')
      loop (Skip s1')     x2             = loop (next1 s1') x2
      loop x1             (Skip s2')     = loop x1          (next2 s2')
      loop Done _                        = False
      loop _    Done                     = False
      loop (Yield x1 s1') (Yield x2 s2') = x1 == x2 &&
                                           loop (next1 s1') (next2 s2')
{-# INLINE [0] eq #-}

cmp :: (Ord a) => Stream a -> Stream a -> Ordering
cmp (Stream next1 s1 _) (Stream next2 s2 _) = loop (next1 s1) (next2 s2)
    where
      loop Done Done                     = EQ
      loop (Skip s1')     (Skip s2')     = loop (next1 s1') (next2 s2')
      loop (Skip s1')     x2             = loop (next1 s1') x2
      loop x1             (Skip s2')     = loop x1          (next2 s2')
      loop Done _                        = LT
      loop _    Done                     = GT
      loop (Yield x1 s1') (Yield x2 s2') =
          case compare x1 x2 of
            EQ    -> loop (next1 s1') (next2 s2')
            other -> other
{-# INLINE [0] cmp #-}

-- | The empty stream.
empty :: Stream a
empty = Stream next () 0
    where next _ = Done
{-# INLINE [0] empty #-}
