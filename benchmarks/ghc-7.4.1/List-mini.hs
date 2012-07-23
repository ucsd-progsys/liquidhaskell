{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP, NoImplicitPrelude, MagicHash #-}
{-# OPTIONS_HADDOCK hide #-}

module GHC.List (
 take, drop
 ) where

import Data.Maybe
import GHC.Base hiding (assert) 
import Language.Haskell.Liquid.Prelude (crash)

{-@ assert take  :: n: {v: Int | v >= 0 } -> xs:[a] -> {v:[a] | len(v) = ((len(xs) < n) ? len(xs) : n) } @-}
{- INLINE [0] take -}
take                   :: Int -> [a] -> [a]
take (I# n#) xs = takeUInt n# xs

takeUInt :: Int# -> [b] -> [b]
takeUInt n xs
  | n >=# 0#  =  take_unsafe_UInt n xs
  | otherwise =  crash False -- []

take_unsafe_UInt :: Int# -> [b] -> [b]
take_unsafe_UInt 0#  _     = []
take_unsafe_UInt mother ls =
  case ls of
    []     -> []
    (x:xs) -> x : take_unsafe_UInt (mother -# 1#) xs

{-@ assert drop        :: n: {v: Int | v >= 0 } -> xs:[a] -> {v:[a] | len(v) = ((len(xs) <  n) ? 0 : len(xs) - n) } @-}
drop                   :: Int -> [a] -> [a]
drop (I# n#) ls
  | n# <# 0#    = ls
  | otherwise   = drop# n# ls
    where
        drop# :: Int# -> [a] -> [a]
        drop# 0# xs      = xs
        drop# _  xs@[]   = xs
        drop# m# (_:xs)  = drop# (m# -# 1#) xs























