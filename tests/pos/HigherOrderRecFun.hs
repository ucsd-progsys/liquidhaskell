module HOF () where

foo :: [a] -> (b -> c) -> (b -> c)
foo []     f = f
foo (x:xs) f = foo xs f

