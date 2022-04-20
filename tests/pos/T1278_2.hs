{-@ LIQUID "--exact-data-cons" @-}

module T1278_2 where

{-@ data List [sz] @-}
data List a = Nil | Cons a (List a)

{-@ measure sz @-}
sz :: List a -> Int
sz Nil = 0
sz (Cons _ Nil) = 1
sz (Cons _ (Cons _ l)) = 2 + sz l
