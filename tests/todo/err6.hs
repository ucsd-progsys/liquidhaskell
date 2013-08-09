-- | Error Message Test: liquid type error

module Err0 where

{-@ zonk :: {v:Int | v = z} @-}
zonk     = (12 :: Int)


