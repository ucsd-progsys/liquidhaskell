module ListSort where

{-@ data LL a <p :: head:a -> v:a -> Bool> = Nil | Cons (h :: a) (t :: LL <p> (a <p h>)) @-}

data LL a = Nil | Cons a (LL a)

{-@ single :: a -> LL <{v:a| v >= head}> a @-}
single :: a -> LL a
single x = Cons x Nil 

