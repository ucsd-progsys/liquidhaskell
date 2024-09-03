{-@ LIQUID "--reflection" @-}

module OpaqueRefl03C where

import OpaqueRefl03D (foobar)

{-@ reflect myfoobar1 @-}
myfoobar1 :: Int -> Int -> Int 
myfoobar1 n m = foobar n m