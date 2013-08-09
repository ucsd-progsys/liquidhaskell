-- | Error Message Test: liquid type error

module Err0 where

{-@ tonk :: {v:Int | (Prop v) = v } @-}
tonk     = (12 :: Int)

