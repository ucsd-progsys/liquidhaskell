{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-# LANGUAGE KindSignatures, DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Haskell.Liquid.FinField where

import Data.Proxy
import GHC.TypeLits
import Language.Haskell.Liquid.Prelude

data FFld (o :: Nat) = FFld { ffToInteger :: Integer } deriving Eq
{-@ embed FFld as FFld_t @-}

{-@ assume val :: forall o. KnownNat o => o : Nat -> n : Integer -> {v:FFld o | v = FF_val n} @-}
{-@ define val                            o          n                           = (FF_val n) @-}
val :: Int -> Integer -> FFld o
val _ n = FFld n

{-@ assume add :: forall o. KnownNat o => x : FFld o -> y : FFld o -> {v:FFld o | v = FF_add x y} @-}
{-@ define add                            x             y                          = (FF_add x y) @-}
add :: forall o. KnownNat o => FFld o -> FFld o -> FFld o
add x y =
  FFld (ffToInteger x + ffToInteger y `mod` liquidAssume (n /= 0) n)
  where
  n = natVal (Proxy :: Proxy o)

{-@ assume mul :: forall o. KnownNat o => x : FFld o -> y : FFld o -> {v:FFld o | v = FF_mul x y} @-}
{-@ define mul                            x             y                          = (FF_mul x y) @-}
mul :: forall o. KnownNat o => FFld o -> FFld o -> FFld o
mul x y = FFld (ffToInteger x * ffToInteger y `mod` liquidAssume (n /= 0) n)
  where
  n = natVal (Proxy :: Proxy o)
