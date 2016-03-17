{-@ measure foo @-}
bar, foo :: [(Int,Int)] -> Int
foo [] = 0
foo (a:as) = fst a + foo as

{-@ fst :: xs:(a, b) -> {v:a | v == fst xs} @-}


{-@ bar :: xs:[(Int, Int)] -> {v:Int | v == foo xs } @-}
bar x = foo x 