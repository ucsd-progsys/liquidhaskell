{-@ LIQUID "--notermination" @-}

module VectorBounds (
    safeLookup
  , unsafeLookup, unsafeLookup'
  , absoluteSum, absoluteSum'
  , absoluteSumNT, goNT
  , dotProduct
  , sparseProduct, sparseProduct'
  ) where

import Prelude      hiding (length)
import Data.List    (foldl')
import Data.Vector  hiding (foldl')

-- | We **specify** bounds safety by *refining* the types

-- module spec Data.Vector where
-- import GHC.Base
-- measure vlen  ::   (Vector a) -> Int
-- assume length :: x:(Vector a) -> {v:Int | v = (vlen x)}
-- assume !      :: x:(Vector a) -> {v:Int | (0 <= v && v < (vlen x))} -> a

-- | An *unsafe* vector lookup function:


{-@ unsafeLookup :: vec:Vector a
                 -> {v: Int | (0 <= v && v < (vlen vec))}
                 -> a
  @-}
unsafeLookup vec index = vec ! index

{-@ safeLookup :: Vector a -> Int -> Maybe a @-}
safeLookup x i
  | 0 <= i && i < length x = Just (x ! i)
  | otherwise              = Nothing


-- | **Predicate Aliases**

{-@ predicate Btwn I Lo Hi = (Lo <= I && I < Hi) @-}
{-@ predicate InBounds I A = (Btwn I 0 (vlen A)) @-}

-- | Now, we can simplify the type for the unsafe lookup function to

{-@ unsafeLookup' :: x:Vector a -> {v:Int | (InBounds v x)} -> a @-}
unsafeLookup' :: Vector a -> Int -> a
unsafeLookup' x i = x ! i



-- | A function that sums the absolute values of the elements of a vector

{-@ absoluteSum :: Vector Int -> {v: Int | 0 <= v}  @-}
absoluteSum       :: Vector Int -> Int
absoluteSum vec   = if 0 < n then go 0 0 else 0
  where
    go acc i
      | i /= n    = go (acc + abz (vec ! i)) (i + 1)
      | otherwise = acc
    n             = length vec

{-@ absoluteSumNT :: Vector Int -> {v: Int | 0 <= v}  @-}
absoluteSumNT     :: Vector Int -> Int
absoluteSumNT vec = goNT vec 0 0 

{-@ goNT          :: vec: (Vector Int) 
                  -> {v:Int | 0 <= v} 
                  -> {v:Int | ((0 <= v) && (v <= (vlen vec))) } 
                  -> {v:Int | 0 <= v} @-}
                 
goNT              :: Vector Int -> Int -> Int -> Int                 
goNT vec acc i
  | i /= n        = goNT vec (acc + abz (vec ! i)) (i + 1)
  | otherwise     = acc
  where n         = length vec




-- | The function `abz` is the absolute value function from [before][ref101].

abz n = if 0 <= n then n else (0 - n)

loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f = go base lo
  where
    go acc i
      | i /= hi   = go (f i acc) (i + 1)
      | otherwise = acc


absoluteSum' vec = if 0 < n then loop 0 n 0 body else 0
  where body     = \i acc -> acc + (vec ! i)
        n        = length vec


-- | Another use of `loop` : compute the `dotProduct` of two vectors.

{-@ dotProduct :: x:(Vector Int) 
               -> y:{v: (Vector Int) | (vlen v) = (vlen x)} 
               -> Int 
  @-}

dotProduct     :: Vector Int -> Vector Int -> Int
dotProduct x y = loop 0 (length x) 0 (\i -> (+ (x ! i) * (y ! i)))



-- | Refinement type alias for **Sparse Vectors**

{-@ type SparseVector a N = [({v: Int | (Btwn v 0 N)}, a)] @-}

-- | A sparse product function

{-@ sparseProduct :: (Num a) => x:(Vector a) 
                             -> SparseVector a {(vlen x)} 
                             -> a 
  @-}

sparseProduct x y  = go 0 y
  where
    go sum ((i, v) : y') = go (sum + (x ! i) * v) y'
    go sum []            = sum


-- | A `foldl` based sparse product

{-@ sparseProduct' :: (Num a) => x:(Vector a) 
                             -> SparseVector a {(vlen x)} 
                             -> a 
  @-}

sparseProduct' x y   = foldl' body 0 y
  where body sum (i, v) = sum + (x ! i) * v

