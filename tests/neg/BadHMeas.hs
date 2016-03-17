
{-@ measure foo @-}
foo :: [(Int,Int)] -> Int
foo [] = 0
foo (a:as) = fst a + foo as