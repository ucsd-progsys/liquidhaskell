{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-# LANGUAGE KindSignatures, DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Haskell.Liquid.FinField where

import Data.Proxy
import GHC.TypeLits
import Language.Haskell.Liquid.Prelude

data FFld (o :: Nat) = FFld { ffToInteger :: Integer } deriving Eq
