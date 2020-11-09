module spec Data.Maybe where

measure isJust' :: Maybe a -> Bool
  isJust' Nothing  = false
  isJust' (Just _) = true

measure isNothing' :: Maybe a -> Bool
  isNothing' Nothing  = true
  isNothing' (Just _) = false

maybe :: v:b -> (a -> b) -> u:(Maybe a) -> {w:b | not (isJust' u) => w == v}
isJust :: v:(Maybe a) -> {b:Bool | b == isJust' v}
isNothing :: v:(Maybe a) -> {b:Bool | b == isNothing' v}
fromJust :: {v:(Maybe a) | isJust' v} -> a
fromMaybe :: v:a -> u:(Maybe a) -> {x:a | isNothing' u => x == v}
