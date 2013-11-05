{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--no-termination" @-}
-- ---------------------------------------------------------------------------
-- |
-- Module      : Data.Vector.Algorithms.Common
-- Copyright   : (c) 2008-2011 Dan Doel
-- Maintainer  : Dan Doel
-- Stability   : Experimental
-- Portability : Portable
--
-- Common operations and utility functions for all sorts

module Data.Vector.Algorithms.Common where

import Language.Haskell.Liquid.Prelude (liquidAssert)

import Prelude hiding (read, length)

import Control.Monad.Primitive

import Data.Vector.Generic.Mutable

import qualified Data.Vector.Primitive.Mutable as PV
import qualified Data.Vector.Primitive.Mutable 

----------------------------------------------------------------------------
-- LIQUID Specifications ---------------------------------------------------
----------------------------------------------------------------------------

-- | Vector Size Measure

{-@ measure vsize :: (v m e) -> Int @-}

-- | Vector Type Aliases
{-@ type NeVec v m e = {v: (v (PrimState m) e) | 0 < (vsize v)} @-}
{-@ type OkIdx X          = {v:Nat | (OkRng v X 0)}         @-}
{-@ type AOkIdx X         = {v:Nat | v <= (vsize X)}        @-}
{-@ type Pos              = {v:Int | v > 0 }                @-}
{-@ type LtIdxOff Off Vec = {v:Nat | v+Off < (vsize Vec)}   @-}
{-@ type LeIdxOff Off Vec = {v:Nat | v+Off <= (vsize Vec)}  @-}

-- | Only mention of ordering
{-@ predicate InRngL V L U = (L <  V && V <= U)                @-}
{-@ predicate InRng  V L U = (L <= V && V <= U)                @-}
{-@ predicate EqSiz  X Y   = (vsize X) = (vsize Y)             @-}

-- | Abstractly defined using @InRng@

{-@ predicate OkOff X B O  = (InRng (B + O) 0 (vsize X))       @-} 
{-@ predicate OkRng V X N  = (InRng V 0 ((vsize X) - (N + 1))) @-}

-- | Assumed Types for Vector

{-@ Data.Vector.Generic.Mutable.length      
      :: (Data.Vector.Generic.Mutable.MVector v a) 
      => x:(v s a) 
      -> {v:Nat | v = (vsize x)} 
  @-}

{-@ Data.Vector.Generic.Mutable.unsafeRead  
      :: (PrimMonad m, Data.Vector.Generic.Mutable.MVector v a) 
      => x:(v (PrimState m) a) 
      -> (OkIdx x) 
      -> m a       
  @-}

{-@ Data.Vector.Generic.Mutable.unsafeWrite 
      :: (PrimMonad m, Data.Vector.Generic.Mutable.MVector v a) 
      => x:(v (PrimState m) a) 
      -> (OkIdx x) 
      -> a 
      -> m () 
  @-}

{-@ Data.Vector.Generic.Mutable.unsafeSwap
      :: (PrimMonad m, Data.Vector.Generic.Mutable.MVector v a) 
      => x:(v (PrimState m) a) 
      -> (OkIdx x) 
      -> (OkIdx x) 
      -> m () 
  @-}

{-@ Data.Vector.Generic.Mutable.unsafeSlice 
      :: Data.Vector.Generic.Mutable.MVector v a 
      => i:Nat 
      -> n:Nat 
      -> {v:(v s a) | (OkOff v i n)} 
      -> {v:(v s a) | (vsize v) = n}  
  @-}

{-@ Data.Vector.Generic.Mutable.unsafeCopy  
      :: (PrimMonad m, Data.Vector.Generic.Mutable.MVector v a) 
      => src:(v (PrimState m) a) 
      -> {dst:(v (PrimState m) a) | (EqSiz src dst)} 
      -> m () 
  @-}

{-@ Data.Vector.Generic.Mutable.new 
      :: (PrimMonad m, Data.Vector.Generic.Mutable.MVector v a) 
      => nINTENDO:Nat 
      -> m {v: (v (PrimState m) a) | (vsize v) = nINTENDO}
  @-}

{-@ Data.Vector.Primitive.Mutable.new 
      :: (PrimMonad m, Data.Vector.Primitive.Mutable.Prim a) 
      => nONKEY:Nat 
      -> m {v: (Data.Vector.Primitive.Mutable.MVector (PrimState m) a) | (vsize v) = nONKEY}
  @-}




{-@ qualif NonEmpty(v:a): 0 < (vsize v)           @-}
{-@ qualif Cmp(v:a, x:b): v < x                   @-}
{-@ qualif OkIdx(v:a, x:b): v <= (vsize x)        @-}
{-@ qualif OkIdx(v:a, x:b): v <  (vsize x)        @-}
{-@ qualif EqSiz(x:a, y:b): (vsize x) = y         @-}
{-@ qualif EqSiz(x:a, y:b): x = (vsize y)         @-}
{-@ qualif EqSiz(x:a, y:b): (vsize x) = (vsize y) @-}
{-@ qualif Plus(v:Int, x:Int, y:Int): v + x = y   @-}

-- TODO: push this type into the signature for `shiftR`. Issue: math on non-num types.
-- TODO: support unchecked `assume`. Currently writing `undefined` to suppress warning
-- {- assume shiftRI :: x:Nat -> {v:Int | v = 1} -> {v:Nat | (x <= 2*v + 1 && 2*v <= x)} @-}
{-@ assume shiftRI :: x:Nat -> s:Nat 
                   -> {v:Nat | (   (s=1 => (2*v <= x && x <= 2*v + 1))
                                && (s=2 => (4*v <= x && x <= 4*v + 3))) } 
  @-}
shiftRI :: Int -> Int -> Int
shiftRI = undefined -- shiftR

{-@ assume shiftLI :: x:Nat -> s:Nat 
                   -> {v:Nat | (   (s = 1 => v = 2 * x) 
                                && (s = 2 => v = 4 * x)) } 
  @-}
shiftLI :: Int -> Int -> Int
shiftLI = undefined -- shiftL
----------------------------------------------------------------------------

-- | A type of comparisons between two values of a given type.
type Comparison e = e -> e -> Ordering

{-@ copyOffset :: (PrimMonad m, MVector v e)
               => from  : (v (PrimState m) e) 
               -> to    : (v (PrimState m) e) 
               -> iFrom : Nat 
               -> iTo   : Nat 
               -> {len  : Nat | ((OkOff from iFrom len) && (OkOff to iTo len))} 
               -> m ()
  @-}
copyOffset :: (PrimMonad m, MVector v e)
           => v (PrimState m) e -> v (PrimState m) e -> Int -> Int -> Int -> m ()
copyOffset from to iFrom iTo len =
  unsafeCopy (unsafeSlice iTo len to) (unsafeSlice iFrom len from)
{-# INLINE copyOffset #-}

{-@ inc :: (PrimMonad m, MVector v Int) => x:(v (PrimState m) Int) -> (OkIdx x) -> m Int @-}
inc :: (PrimMonad m, MVector v Int) => v (PrimState m) Int -> Int -> m Int
inc arr i = unsafeRead arr i >>= \e -> unsafeWrite arr i (e+1) >> return e
{-# INLINE inc #-}


-- LIQUID: flipping order to allow dependency.
-- shared bucket sorting stuff
{-@ countLoop :: (PrimMonad m, MVector v e)
              => (v (PrimState m) e) 
              -> count:(PV.MVector (PrimState m) Int) 
              -> (e -> (OkIdx count)) ->  m ()
  @-}
countLoop :: (PrimMonad m, MVector v e)
          => (v (PrimState m) e) -> (PV.MVector (PrimState m) Int) 
          -> (e -> Int) ->  m ()
countLoop src count rdx = set count 0 >> go len 0
 where
 len = length src
 go (m :: Int) i
   | i < len   = let lenSrc = length src 
                 in ({- liquidAssert (i < lenSrc) $ -} unsafeRead src i) >>= inc count . rdx >> go (m-1) (i+1)
   | otherwise = return ()
{-# INLINE countLoop #-}























