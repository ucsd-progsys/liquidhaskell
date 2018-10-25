{-@ type IntN N = {v:Int | v = N} @-}

{-@ foo :: n:Int ~> m:Int ~> (() -> IntN n) -> (() -> IntN m) -> IntN {n+m} @-}
foo :: (() -> Int) -> (() -> Int) -> Int
foo f g = f () + g ()

{-@ test3 :: m:Int -> IntN {m+2} @-}
test3 m = foo (\_ -> m) (\_ -> 2)
