-- | Top-level module for the multiple import test when the top-level redefines the assume reflect
-- | We reuse the modules from test 02
-- Import hierarchy:
--                 A
--             /       \
--            /         \
--           B           C
--            \         /
--             \       /
--                03
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module AssmRefl03 where

import AssmRefl02A (foobar)
import AssmRefl02B (myfoobar)
import AssmRefl02C (myfoobar)

{-@ assume reflect foobar as myfoobar3 @-}
{-@ reflect myfoobar3 @-}
myfoobar3 :: Int -> Bool
myfoobar3 n = n `mod` 2 == 0

{-@ test :: { foobar 2 } @-}
test :: ()
test = ()