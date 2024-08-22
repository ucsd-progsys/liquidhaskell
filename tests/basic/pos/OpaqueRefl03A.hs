-- Checking the behavior of opaque reflection in case two imported modules (B and C here) opaque reflected
-- the same module from a common import D. The two opaque reflections of the same variable should be merged
-- and considered the same.

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module OpaqueRefl03A where

import OpaqueRefl03B
import OpaqueRefl03C

{-@ reflect myfoobar3 @-}
myfoobar3 :: Int -> Int -> Int 
myfoobar3 n m = myfoobar1 n m + myfoobar2 n m

{-@ usefulLemma :: n: Int -> m: Int -> {myfoobar3 n m == 2 * myfoobar1 n m} @-}
usefulLemma :: Int -> Int -> ()
usefulLemma n m = ()