{-@ type IntN N = {v:Int | v = N} @-}

{-@ foo :: n:Int ~> (() -> IntN n) -> IntN {n+2} @-}
foo :: (() -> Int) -> Int
foo f = 1 + f ()

{-@ test1 :: IntN 12 @-}
test1 = foo (\_ -> 10)


{-@ test4 :: IntN 10 @-}
test4 = foo (const (10))
