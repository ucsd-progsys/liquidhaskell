module MultiRel where

foo :: Int -> Int
foo x = x

{-@ relational foo ~ foo :: x:Int -> Int ~ y:Int -> Int ~~ x < y => r1 x < r2 y @-}
{-@ relational foo ~ foo :: x:Int -> Int ~ y:Int -> Int ~~ x = y => r1 x = r2 y @-}

bar :: Int -> Int
bar x = foo x

{-@ relational bar ~ bar :: x:Int -> Int ~ y:Int -> Int ~~ true => (x <= y <=> r1 x <= r2 y) @-}