{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UnboxedTuples #-}

module UnboxedTuplesAndTH where

import GHC.Int
import Language.Haskell.TH.Syntax

foo = let (# x, y #) = (# 1#, 1# #) in I# x

bar :: Q Exp
bar = [| 1 + 2|]

