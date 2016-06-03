{-# LANGUAGE QuasiQuotes #-}

module Nats where

import LiquidHaskell

[lq| nats :: Show s => s -> [{ v:Int | 0 <= v }] |]
nats _ = [0,1,2,3,4,5,6,7,8,9,10]

[lq| myId :: x:a -> { v:a | v = x } |]
myId x = x

