{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}
-- |
-- Module      : Data.Text.Fusion.Internal
-- Copyright   : (c) Roman Leshchinskiy 2008,
--               (c) Bryan O'Sullivan 2009
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : portable
--
-- Size hints.

module Data.Text.Fusion.Size
    (
      Size(..)
    , exactly
    , exactSize
    , maxSize
    , unknownSize
    , smaller
    , larger
    , upperBound
    , isEmpty
    ) where

#if defined(ASSERTS)
import Control.Exception (assert)
#endif

data Size = Exact {-# UNPACK #-} !Int -- ^ Exact size.
          | Max   {-# UNPACK #-} !Int -- ^ Upper bound on size.
          | Unknown                   -- ^ Unknown size.
            deriving (Eq, Show)

{-@ measure getSize :: Data.Text.Fusion.Size.Size -> Int
    getSize (Data.Text.Fusion.Size.Exact n) = n
    getSize (Data.Text.Fusion.Size.Max   n) = n
  @-}
{-@ measure isUnknown :: Data.Text.Fusion.Size.Size -> Prop
    isUnknown (Data.Text.Fusion.Size.Exact n) = false
    isUnknown (Data.Text.Fusion.Size.Max   n) = false
    isUnknown (Data.Text.Fusion.Size.Unknown) = true
  @-}
{-@ qualif IsUnknown(v:Data.Text.Fusion.Size.Size) : (isUnknown v) @-}
{-@ qualif IsKnown(v:Data.Text.Fusion.Size.Size) : not (isUnknown v) @-}

{-@ invariant {v:Data.Text.Fusion.Size.Size | (getSize v) >= 0} @-}

exactly :: Size -> Maybe Int
exactly (Exact n) = Just n
exactly _         = Nothing
{-# INLINE exactly #-}

{-@ exactSize :: n:Nat
              -> {v:Data.Text.Fusion.Size.Size |
                   (((getSize v) = n) && (not (isUnknown v)))} @-}
exactSize :: Int -> Size
exactSize n =
#if defined(ASSERTS)
    assert (n >= 0)
#endif
    Exact n
{-# INLINE exactSize #-}

{-@ maxSize :: n:Nat
            -> {v:Data.Text.Fusion.Size.Size |
                 (((getSize v) = n) && (not (isUnknown v)))} @-}
maxSize :: Int -> Size
maxSize n =
#if defined(ASSERTS)
    assert (n >= 0)
#endif
    Max n
{-# INLINE maxSize #-}

{-@ unknownSize :: {v:Data.Text.Fusion.Size.Size | (isUnknown v)} @-}
unknownSize :: Size
unknownSize = Unknown
{-# INLINE unknownSize #-}

instance Num Size where
    (+) = addSize
    (-) = subtractSize
    (*) = mulSize

    fromInteger = f where f = Exact . fromInteger
                          {-# INLINE f #-}

add :: Int -> Int -> Int
add m n | mn >=   0 = mn
        | otherwise = overflowError
  where mn = m + n
{-# INLINE add #-}

addSize :: Size -> Size -> Size
addSize (Exact m) (Exact n) = Exact (add m n)
addSize (Exact m) (Max   n) = Max   (add m n)
addSize (Max   m) (Exact n) = Max   (add m n)
addSize (Max   m) (Max   n) = Max   (add m n)
addSize _          _       = Unknown
{-# INLINE addSize #-}

subtractSize :: Size -> Size -> Size
subtractSize   (Exact m) (Exact n) = Exact (max (m-n) 0)
subtractSize   (Exact m) (Max   _) = Max   m
subtractSize   (Max   m) (Exact n) = Max   (max (m-n) 0)
subtractSize a@(Max   _) (Max   _) = a
subtractSize a@(Max   _) Unknown   = a
subtractSize _         _           = Unknown
{-# INLINE subtractSize #-}

mul :: Int -> Int -> Int
mul m n
    | m <= maxBound `div` n = m * n
    | otherwise             = overflowError
{-# INLINE mul #-}

mulSize :: Size -> Size -> Size
mulSize (Exact m) (Exact n) = Exact (mul m n)
mulSize (Exact m) (Max   n) = Max   (mul m n)
mulSize (Max   m) (Exact n) = Max   (mul m n)
mulSize (Max   m) (Max   n) = Max   (mul m n)
mulSize _          _        = Unknown
{-# INLINE mulSize #-}

-- | Minimum of two size hints.
smaller :: Size -> Size -> Size
smaller   (Exact m) (Exact n) = Exact (m `min` n)
smaller   (Exact m) (Max   n) = Max   (m `min` n)
smaller   (Exact m) Unknown   = Max   m
smaller   (Max   m) (Exact n) = Max   (m `min` n)
smaller   (Max   m) (Max   n) = Max   (m `min` n)
smaller a@(Max   _) Unknown   = a
smaller   Unknown   (Exact n) = Max   n
smaller   Unknown   (Max   n) = Max   n
smaller   Unknown   Unknown   = Unknown
{-# INLINE smaller #-}

-- | Maximum of two size hints.
{-@ larger :: s1:Data.Text.Fusion.Size.Size
           -> s2:Data.Text.Fusion.Size.Size
           -> {v:Data.Text.Fusion.Size.Size |
                 ((not ((isUnknown s1) || (isUnknown s2))) =>
                  (Max (getSize v) (getSize s1) (getSize s2)))}
  @-}

larger :: Size -> Size -> Size
larger   (Exact m)   (Exact n)             = Exact (m `max` n)
larger a@(Exact m) b@(Max   n) | m >= n    = a
                               | otherwise = b
larger a@(Max   m) b@(Exact n) | n >= m    = b
                               | otherwise = a
larger   (Max   m)   (Max   n)             = Max   (m `max` n)
larger _             _                     = Unknown
{-# INLINE larger #-}

-- | Compute the maximum size from a size hint, if possible.
{-@ upperBound :: k:Nat -> s:Data.Text.Fusion.Size.Size
               -> {v:Nat | v = ((isUnknown s) ? k : (getSize s))}
  @-}
upperBound :: Int -> Size -> Int
upperBound _ (Exact n) = n
upperBound _ (Max   n) = n
upperBound k _         = k
{-# INLINE upperBound #-}

{-@ isEmpty :: s:Data.Text.Fusion.Size.Size
            -> {v:Bool | ((Prop v) <=> ((not (isUnknown s) && ((getSize s) = 0))))}
  @-}
isEmpty :: Size -> Bool
isEmpty (Exact n) = n <= 0
isEmpty (Max   n) = n <= 0
isEmpty _         = False
{-# INLINE isEmpty #-}

{-@ overflowError :: Int @-}
overflowError :: Int
overflowError = error "Data.Text.Fusion.Size: size overflow"
