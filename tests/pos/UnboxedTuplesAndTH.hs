{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UnboxedTuples #-}

module Blank where

import GHC.Int
import Language.Haskell.TH.Syntax

foo = let (# x, y #) = (# 1#, 1# #) in I8# x

bar :: Q Exp
bar = [| 1 + 2|]

