{- | By Gabriel Gonzalez, from:
     http://www.haskellforall.com/2015/12/compile-time-memory-safety-using-liquid.html
-}

module BinarySearch (binarySearch) where

import Data.Vector as V

binarySearch :: Ord a => a -> V.Vector a -> Maybe Int
binarySearch x v =
    if V.length v == 0
    then Nothing
    else loop x v 0 (V.length v - 1)

midpoint :: Int -> Int -> Int
midpoint lo hi = (lo + hi) `div` 2

{-@
loop
    :: Ord a
    => x  : a
    -> v  : V.Vector a
    -> lo : { lo : Int | 0  <= lo && lo < vlen v }
    -> hi : { hi : Int | lo <= hi && hi < vlen v }
    -> Maybe Int
    / [hi - lo]
@-}
loop :: Ord a => a -> V.Vector a -> Int -> Int -> Maybe Int
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
