module T1278 where

data List a = Nil | Cons a (List a)

sz :: List a -> Int
sz Nil = 0
sz (Cons _ Nil) = 1
sz (Cons _ (Cons _ l)) = 2 + sz l
