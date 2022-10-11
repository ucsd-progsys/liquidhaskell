{-@ LIQUID "--expect-any-error" @-}
{-# LANGUAGE QuasiQuotes #-}

module QQTySig where

import LiquidHaskell

[lq| nats :: [{ v:Int | 0 <= v }] |]
nats = [-1,0,1,2,3,4,5,6,7,8,9,10]

