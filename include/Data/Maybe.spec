module spec Data.Maybe where

maybe :: v:b -> (a -> b) -> u:(Maybe a) -> {w:b | not (isJust u) => w == v}
isJust :: v:(Maybe a) -> {b:Bool | b == isJust v}
isNothing :: v:(Maybe a) -> {b:Bool | not (isJust v) == b}
fromJust :: {v:(Maybe a) | isJust v} -> a
fromMaybe :: v:a -> u:(Maybe a) -> {x:a | not (isJust u) => x == v}
