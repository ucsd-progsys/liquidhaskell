{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Internal.Data.Maybe_LHAssumptions where

import GHC.Types_LHAssumptions()
import GHC.Internal.Data.Maybe
import GHC.Internal.Maybe

{-@
assume GHC.Internal.Data.Maybe.maybe :: v:b -> (a -> b) -> u:(Maybe a) -> {w:b | not (isJust u) => w == v}
assume GHC.Internal.Data.Maybe.isNothing :: v:(Maybe a) -> {b:Bool | not (isJust v) == b}
assume GHC.Internal.Data.Maybe.fromMaybe :: v:a -> u:(Maybe a) -> {x:a | not (isJust u) => x == v}

assume GHC.Internal.Data.Maybe.isJust :: v:(Maybe a) -> {b:Bool | b == isJust v}
measure isJust :: Maybe a -> Bool
  isJust (Just x)  = true
  isJust (Nothing) = false

assume GHC.Internal.Data.Maybe.fromJust :: {v:(Maybe a) | isJust v} -> a
measure fromJust :: Maybe a -> a
  fromJust (Just x) = x
@-}
