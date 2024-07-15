-- | Top-level module for the multiple import test
-- Import hierarchy:
--                 A
--             /       \
--            /         \
--           B           C
--            \         /
--             \       /
--                 D
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module AssmRefl02D where

import AssmRefl02A (foobar)
import AssmRefl02B (myfoobar)
import AssmRefl02C (myfoobar)

{-@ test :: { foobar 3 } @-}
test :: ()
test = ()