{-@ LIQUID "--expect-error-containing=Unknown logic name `x`" @-}
module UnboundVarInAssume where

{-@ assume incr :: Int -> {v : Int | v == x} @-}
incr :: Int -> Int
incr x = x + 1
