{-@ LIQUID "--expect-error-containing=Illegal type specification for `UnboundFunInSpec.three`" @-}
module UnboundFunInSpec () where

cnt   :: Int -> Int
cnt 0 = 0
cnt i = 1 + cnt (i-1)

{-@ three :: {v:Int | (cnt v) = 3} @-}
three :: Int
three = 15
