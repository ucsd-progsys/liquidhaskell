{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.Maybe_LHAssumptions where

import Data.Maybe
import GHC.Types_LHAssumptions ()

{-@
assume maybe :: v:b -> (a -> b) -> u:(Maybe a) -> {w:b | not (isJust u) => w == v}
assume isNothing :: v:(Maybe a) -> {b:Bool | not (isJust v) == b}
assume fromMaybe :: v:a -> u:(Maybe a) -> {x:a | not (isJust u) => x == v}

assume isJust :: v:(Maybe a) -> {b:Bool | b == isJust v}
measure isJust :: Maybe a -> Bool
  isJust (Just x)  = true
  isJust (Nothing) = false

assume fromJust :: {v:(Maybe a) | isJust v} -> a
measure fromJust :: Maybe a -> a
  fromJust (Just x) = x
@-}
