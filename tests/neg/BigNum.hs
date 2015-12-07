module BigNum where

{-@ type Foo = { v : Integer | 0 <= v && v < 4611686018427387903 * 8 } @-}

{-@ f :: i : Foo -> { o : Foo | i < o } @-}
f :: Integer -> Integer
f i = i * 2
