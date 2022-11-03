{-@ LIQUID "--expect-any-error" @-}
module BuiltInFib where

fib :: Int -> Int
fib x | x <= 1 = 1
fib x = fib (x - 1) + fib (x - 2)

{-@ relational fib ~ fib :: {x1:_ -> {v:Int|v >= 1} ~ x2:_ -> {v:Int|v >= 1}
                         | x1 <= x2 :=> r1 x1 < r2 x2 } @-}

