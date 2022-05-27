{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP,  MagicHash #-}
{-# OPTIONS_HADDOCK hide #-}

module PrimInt0 (ptake, mtake, ztake, itake) where

import Data.Maybe
import GHC.Base

{-@ ztake  :: n: {v: Int# | 0 <= v} -> {v: Int | v = n } @-}
ztake :: Int# -> Int
ztake 0# = 0
ztake n# = 1 + ztake (n# -# 1#)

{-@ itake  :: n: {v: Int | 0 <= v} -> {v: Int | v = n } @-}
itake :: Int -> Int
itake 0 = 0
itake n = 1 + itake (n - 1)

{-@ ptake  :: n: {v: GHC.Prim.Int# | 0 <= v} -> {v:[a] | ((len v) >= n)} -> {v:[a] | (len(v) = n)} @-}
ptake :: Int# -> [a] -> [a]
ptake 0# _      = []
ptake n# (x:xs) = x : ptake (n# -# 1#) xs

{-@ mtake  :: n: {v: Int | 0 <= v} -> {v:[a]|((len v) >= n)} -> {v:[a] | (len(v) = n)} @-}
mtake          :: Int -> [a] -> [a]
mtake 0 _      = []
mtake n (x:xs) = x : mtake (n - 1) xs




















