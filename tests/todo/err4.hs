-- | Error Message Test: liquid type error

module Err0 where

{-@ zonk :: {v:Int | v = 0} @-}
zonk     = (12 :: Int)
