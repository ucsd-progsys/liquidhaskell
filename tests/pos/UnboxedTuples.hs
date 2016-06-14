{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
module Blank where

import GHC.Int

foo = let (# x, y #) = (# 1#, 1# #) in I8# x

