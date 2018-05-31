{-@ type IntN N = {v:Int | v = N} @-}

{-@ foo :: n:Int ~> (() -> IntN n) -> IntN {n+1} @-}
foo :: (() -> Int) -> Int
foo f = 1 + f ()

{-@ test3 :: m:Int -> IntN {m+2} @-}
test3 m = foo (\_ -> m+1)

