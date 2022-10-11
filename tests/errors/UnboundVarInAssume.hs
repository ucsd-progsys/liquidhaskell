{-@ LIQUID "--expect-error-containing=Illegal type specification for `UnboundVarInAssume.incr`" @-}
module UnboundVarInAssume where

{-@ assume incr :: Int -> {v : Int | v == x} @-}
incr :: Int -> Int
incr x = x + 1
