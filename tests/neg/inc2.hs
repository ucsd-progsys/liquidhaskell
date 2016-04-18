-- ISSUE #671
--
-- | ISSUE would be nice to have error reported at `x-1` and NOT the `inc`
--   note that the right place gets shown if you comment out the `inc 0 = 1`

module Inc where

{-@ inc :: x:Int -> {v:Int | v > x} @-}
inc :: Int -> Int
inc 0 = 1
inc x = x - 1
