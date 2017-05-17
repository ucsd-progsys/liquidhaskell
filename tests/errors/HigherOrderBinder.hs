{-@ foo :: a: Int -> f: (Int -> Int) -> {v : Int | v = 123 + (f a) } @-}
foo :: Int -> (Int -> Int) -> Int
foo a f = f a