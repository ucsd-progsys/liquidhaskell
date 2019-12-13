{-@ LIQUID "--anf" @-}

{-@ type IntN N = {v:Int | v = N} @-}

{-@ foo :: n:Int ~> (() -> IntN n) -> IntN {n+1} @-}
foo :: (() -> Int) -> Int
foo f = 1 + f ()

{-@ test1 :: IntN 11 @-}
test1 = foo (\_ -> 10)

{-@ test2 :: m:Int -> IntN {m+1} @-}
test2 m = foo (\_ -> m)

{-@ test4 :: IntN 11 @-}
test4 = foo (const (10))
