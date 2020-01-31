{-@ head :: {xs:[a] | len xs > 0} -> a @-}
head :: [a] -> a
head (x : _) = x
head []      = error "error"