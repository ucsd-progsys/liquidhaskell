{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-# LANGUAGE KindSignatures, DataKinds #-}

module Language.Haskell.Liquid.FinField where

import GHC.TypeLits

newtype FFld (o :: Nat) = FFld { ffToInteger :: Integer } deriving Eq

-- see /tests/pos/FF17.hs and /tests/pos/FF2131.hs for usage examples
