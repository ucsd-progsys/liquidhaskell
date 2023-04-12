{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.Maybe_LHAssumptions where

import GHC.Types_LHAssumptions()
import Data.Maybe

{-@
assume Data.Maybe.maybe :: v:b -> (a -> b) -> u:(GHC.Maybe.Maybe a) -> {w:b | not (isJust u) => w == v}
assume Data.Maybe.isNothing :: v:(GHC.Maybe.Maybe a) -> {b:Bool | not (isJust v) == b}
assume Data.Maybe.fromMaybe :: v:a -> u:(GHC.Maybe.Maybe a) -> {x:a | not (isJust u) => x == v}

assume Data.Maybe.isJust :: v:(GHC.Maybe.Maybe a) -> {b:Bool | b == isJust v}
measure isJust :: GHC.Maybe.Maybe a -> Bool
  isJust (GHC.Maybe.Just x)  = true
  isJust (GHC.Maybe.Nothing) = false

assume Data.Maybe.fromJust :: {v:(GHC.Maybe.Maybe a) | isJust v} -> a
measure fromJust :: GHC.Maybe.Maybe a -> a
  fromJust (GHC.Maybe.Just x) = x
@-}
