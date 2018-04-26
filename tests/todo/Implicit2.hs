{-@ type IntN N = {v:Int | v = N} @-}

{-@ foo :: n:Int ~> (() -> IntN n) -> IntN {n+1} @-}
foo :: (() -> Int) -> Int
foo f = 1 + f ()

{-@ test2 :: m:Int -> IntN {m+1} @-}
test2 m = foo (\_ -> m)

{-@ test3 :: m:Int -> IntN {m+2} @-}
test3 m = foo (\_ -> m+1)

{-@ bar :: IntN 3 @-}
bar = foo (\_ -> foo (\_ -> 1))

