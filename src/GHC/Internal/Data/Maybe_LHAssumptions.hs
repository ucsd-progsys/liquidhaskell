{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Internal.Data.Maybe_LHAssumptions where

import GHC.Types_LHAssumptions()
import Data.Maybe

{-@
assume GHC.Internal.Data.Maybe.maybe :: v:b -> (a -> b) -> u:(GHC.Internal.Maybe.Maybe a) -> {w:b | not (isJust u) => w == v}
assume GHC.Internal.Data.Maybe.isNothing :: v:(GHC.Internal.Maybe.Maybe a) -> {b:Bool | not (isJust v) == b}
assume GHC.Internal.Data.Maybe.fromMaybe :: v:a -> u:(GHC.Internal.Maybe.Maybe a) -> {x:a | not (isJust u) => x == v}

assume GHC.Internal.Data.Maybe.isJust :: v:(GHC.Internal.Maybe.Maybe a) -> {b:Bool | b == isJust v}
measure isJust :: GHC.Internal.Maybe.Maybe a -> Bool
  isJust (GHC.Internal.Maybe.Just x)  = true
  isJust (GHC.Internal.Maybe.Nothing) = false

assume GHC.Internal.Data.Maybe.fromJust :: {v:(GHC.Internal.Maybe.Maybe a) | isJust v} -> a
measure fromJust :: GHC.Internal.Maybe.Maybe a -> a
  fromJust (GHC.Internal.Maybe.Just x) = x
@-}
