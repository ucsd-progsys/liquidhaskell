{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
-- Tests that non-termination is detected when div is used in the
-- argument of a recursive call.
module Div where

iterateTo0 :: Int -> Int
iterateTo0 0 = 0
iterateTo0 n = iterateTo0 (div n 2)

{-@ test :: {v:Int | v == 0} @-}
test = iterateTo0 (-1)

{-@ test2 :: {v:Int | v == 0} @-}
test2 = iterateTo0 1024

{-@ test3 :: {v:Int | v == 0} @-}
test3 = iterateTo0 9

{-@ test4 :: {v:Int | v == 0} @-}
test4 = iterateTo0 0
