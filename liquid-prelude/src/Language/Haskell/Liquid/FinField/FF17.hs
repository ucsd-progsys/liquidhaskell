{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-# LANGUAGE KindSignatures, DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Haskell.Liquid.FinField where

import Data.Proxy
import GHC.TypeLits
import Language.Haskell.Liquid.Prelude
import Language.Haskell.Liquid.FinField

-- instantiate FFld for a specific prime value of 17
data FF17 = FF17 { toFFld :: FFld 17 }
{-@ embed FF17 as (FFld_t '17) @-}

{-@ assume val :: n : Integer -> {v:FF17 | v = FF_val n} @-}
{-@ define val    n                          = (FF_val n) @-}
val :: Integer -> FF17
val n = FF17 (FFld (n `mod` 17))

{-@ assume add :: x : FF17 -> y : FF17 -> {v:FF17 | v = FF_add x y} @-}
{-@ define add    x           y                      = (FF_add x y) @-}
add :: FF17 -> FF17 -> FF17
add x y = FF17 (FFld (ffToInteger (toFFld x) + ffToInteger (toFFld y) `mod` 17))

{-@ assume mul :: x : FF17 -> y : FF17 -> {v:FF17 | v = FF_mul x y} @-}
{-@ define mul    x           y                      = (FF_mul x y) @-}
mul :: FF17 -> FF17 -> FF17
mul x y = FF17 (FFld (ffToInteger (toFFld x) * ffToInteger (toFFld y) `mod` 17))
