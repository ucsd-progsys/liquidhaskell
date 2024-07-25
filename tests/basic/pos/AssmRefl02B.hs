-- | Assume reflect import test
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module AssmRefl02B where

import AssmRefl02A (foobar)

{-@ reflect myfoobar @-}
{-@ assume reflect foobar as myfoobar @-}
myfoobar :: Int -> Bool
myfoobar n = n `mod` 2 == 0

{-@ mytest :: { foobar 4 } @-} 
mytest :: ()
mytest = ()