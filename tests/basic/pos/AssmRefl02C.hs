-- | Assume reflect import test
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module AssmRefl02C where

import AssmRefl02A (foobar)

{-@ reflect myfoobar @-}
{-@ assume reflect foobar as myfoobar @-}
myfoobar :: Int -> Bool 
myfoobar n = n `mod` 2 == 1

{-@ mytest :: { foobar 5 } @-} 
mytest :: ()
mytest = ()