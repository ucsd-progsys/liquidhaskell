{-@ LIQUID "--prune-unsorted" @-}

{-@ measure foo @-}
bar, foo :: [(Int, Int)] -> Int
foo [] = 0
foo (a:as) = myFst a + foo as

{-@ measure myFst @-}
myFst :: (a, b) -> a
myFst (x, y) = x

{-@ bar :: xs:[(Int, Int)] -> {v:Int | v == foo xs } @-}
bar x = foo x
