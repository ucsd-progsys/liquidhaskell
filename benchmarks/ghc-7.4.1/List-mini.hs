{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP, NoImplicitPrelude, MagicHash #-}
{-# OPTIONS_HADDOCK hide #-}

module GHC.List (
 take, drop, foo
 ) where

import Data.Maybe
import GHC.Base hiding (assert) 
import Language.Haskell.Liquid.Prelude (liquidAssert, liquidError) 


{-@ assert foo :: n: {v: Int | v >= 0 } -> Bool @-}
foo (I# n#) = fooUInt n#

fooUInt :: Int# -> Bool
fooUInt n 
  | n >=# 0#  = fooUInt_unsafe n
  | otherwise = liquidAssert False False

fooUInt_unsafe 0# = True
fooUInt_unsafe n  = liquidAssert (n ># 0#) True     -- GET THIS WORKING

{-@ assert take  :: n: {v: Int | v >= 0 } -> xs:[a] -> {v:[a] | len(v) = ((len(xs) < n) ? len(xs) : n) } @-}
{- INLINE [0] take -}
take            :: Int -> [a] -> [a]
take (I# n#) xs = takeUInt n# xs

takeUInt :: Int# -> [a] -> [a]
takeUInt n xs
  | n >=# 0#  =  take_unsafe_UInt n xs
  | otherwise =  liquidAssert False []

take_unsafe_UInt :: Int# -> [a] -> [a]
take_unsafe_UInt 0#  _     = []
take_unsafe_UInt n ls      =
  case ls of
    []     -> []
    (x:xs) -> x : take_unsafe_UInt (n -# 1#) xs

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

















