module SubRef2 where

{-@ foo :: Nat -> Nat @-}
foo :: Int -> Int
foo x = x

{-@ relational foo ~ foo :: x:Nat -> _ ~ y:Nat -> _ ~~ true => x = r1 x && y = r2 y @-}

{-@ bar :: Nat -> Nat @-}
bar :: Int -> Int
bar x = foo x

{-@ relational bar ~ bar :: x:Nat -> _ ~ y:Nat -> _ ~~ x = y => r1 x = r2 y @-}