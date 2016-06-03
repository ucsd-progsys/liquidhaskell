{-# LANGUAGE QuasiQuotes #-}

module Nats where

import LiquidHaskell

[lq| type MyNat = { v:Int | 0 <= v } |]
[lq| type MyList a N = { v:[a] | (len v) = N } |]

[lq| nats :: MyList MyNat 11 |]
nats = [0,1,2,3,4,5,6,7,8,9,10]

