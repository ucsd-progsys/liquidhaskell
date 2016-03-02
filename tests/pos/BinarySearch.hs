{- | By Gabriel Gonzalez, from:
     http://www.haskellforall.com/2015/12/compile-time-memory-safety-using-liquid.html
-}

module BinarySearch (binarySearch) where

import Data.Vector as Vector

binarySearch :: Ord a => a -> Vector a -> Maybe Int
binarySearch x v =
    if Vector.length v == 0
    then Nothing
    else loop x v 0 (Vector.length v - 1)

midpoint :: Int -> Int -> Int
midpoint lo hi = (lo + hi) `div` 2

{-@
loop
    :: Ord a
    => x  : a
    -> v  : Vector a
    -> lo : { lo : Int | 0  <= lo && lo < vlen v }
    -> hi : { hi : Int | lo <= hi && hi < vlen v }
    -> Maybe Int
    / [hi - lo]
@-}
loop :: Ord a => a -> Vector a -> Int -> Int -> Maybe Int
loop x v lo hi = do
    let mid = lo + ((hi - lo) `div` 2) -- midpoint lo hi
    if x < v ! mid
    then do
        let hi' = mid - 1
        if lo <= hi'
        then loop x v lo hi'
        else Nothing
    else if v ! mid < x
    then do
        let lo' = mid + 1
        if lo' <= hi
        then loop x v lo' hi
        else Nothing
    else Just mid
