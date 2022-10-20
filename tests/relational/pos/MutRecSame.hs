module MutRecSame where

{-@ relational foo ~ foo :: n1:_ -> _ ~ n2:_ -> _ | n1 = n2 => r1 n1 = 0 && r2 n2 = 0 @-}
{-@ foo :: n:_ -> _ / [if n >= 0 then n else 0, 1] @-}
foo :: Int -> Int
foo n = bar (n - 1)


{-@ relational bar ~ bar :: n1:_ -> _ ~ n2:_ -> _ | n1 = n2 => r1 n1 = 0 && r2 n2 = 0 @-}
{-@ bar :: n:_ -> _ / [if n >= 0 then n else 0, 0] @-}
bar :: Int -> Int
bar n | n <= 0 = 0
bar n = foo (n - 1)