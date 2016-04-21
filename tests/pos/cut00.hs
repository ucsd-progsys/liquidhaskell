module Cut (foo0) where

{-@ foo0 :: Nat -> Nat @-}

foo0 x = 1 + foo1 x
foo1 x = 1 + foo2 x
foo2 x = 1 + foo3 x
foo3 x = 1 + foo4 x
foo4 x = 1 + foo5 x
foo5 x = 1 + foo  x

foo :: Int -> Int
foo x = 1 + x

bar :: Int -> Int
bar y = y + 10

-- foo x = 1 + foo (x - 1)
