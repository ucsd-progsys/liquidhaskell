module spec Data.Maybe where

import GHC.Types
import GHC.Maybe

maybe :: v:b -> (a -> b) -> u:(GHC.Maybe.Maybe a) -> {w:b | not (isJust u) => w == v}
isNothing :: v:(GHC.Maybe.Maybe a) -> {b:Bool | not (isJust v) == b}
fromMaybe :: v:a -> u:(GHC.Maybe.Maybe a) -> {x:a | not (isJust u) => x == v}

measure isJust :: GHC.Maybe.Maybe a -> Bool
  isJust (GHC.Maybe.Just x)  = true
  isJust (GHC.Maybe.Nothing) = false

fromJust :: {v:(GHC.Maybe.Maybe a) | isJust v} -> a
measure fromJust :: GHC.Maybe.Maybe a -> a
  fromJust (GHC.Maybe.Just x) = x
