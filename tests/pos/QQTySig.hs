{-# LANGUAGE QuasiQuotes #-}

module Nats where

import LiquidHaskell

[lq| nats :: [{ v:Int | 0 <= v }] |]
nats = [0,1,2,3,4,5,6,7,8,9,10]

