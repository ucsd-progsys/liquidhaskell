{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--no-termination" @-}

module BinarySearchOverflow where

import Prelude hiding (Num(..))
import CheckedNum 
import Data.Vector as V
import Language.Haskell.Liquid.Prelude (liquidAssert) 

{-@ invariant {v:V.Vector a | 0 <= vlen v && BoundInt (vlen v)} @-}

binarySearch :: Ord a => a -> V.Vector a -> Maybe Int
binarySearch x v 
  | 0 < n     = loop x v 0 (n - 1)
  | otherwise = Nothing 
  where n     = V.length v

{-@ type Idx Vec = {v:Nat | v < vlen Vec} @-}

{-@ type BoundNat = {v:Nat | BoundInt v} @-}

{-@ loop :: Ord a => a -> vec:V.Vector a -> lo:Idx vec -> {hi:Idx vec | lo <= hi} -> Maybe Nat @-}
loop :: Ord a => a -> V.Vector a -> Int -> Int -> Maybe Int
loop x v lo hi = do
    -- let mid = lo + ((hi - lo) `div` 2) -- SAFE
    let mid =  (hi + lo) `div` 2       -- UNSAFE
    if x < v ! mid
    then do
        let hi' = mid - 1
        if lo <= hi'
        then loop x v lo hi'
        else Nothing
    else if v ! mid < x
    then do
        let lo' = mid + 1 -- incr mid
        if lo' <= hi
        then loop x v lo' hi
        else Nothing
    else Just mid
    


