{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
module UnboxedTuples where

import GHC.Int

foo = let (# x, y #) = (# 1#, 1# #) in I# x

