{-@ LIQUID "--reflection" @-}

module OpaqueRefl03B where

import OpaqueRefl03D (foobar)

{-@ measure azazepoia :: Int -> Int -> Int @-}

{-@ reflect myfoobar2 @-}
myfoobar2 :: Int -> Int -> Int 
myfoobar2 n m = foobar n m