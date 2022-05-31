{-@ LIQUID "--expect-any-error" @-}
{-# LANGUAGE QuasiQuotes #-}

module QQTySyn1 where

import LiquidHaskell

[lq| type MyNat = { v:Int | 0 <= v } |]
[lq| type MyList a N = { v:[a] | (len v) = N } |]

[lq| nats :: MyList MyNat 12 |]
nats = [0,1,2,3,4,5,6,7,8,9,10]

