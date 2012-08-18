module ListSort where

{-@ data LL a <p :: a -> a -> Bool> = Nil | Cons (head :: a) (t :: LL <p> (a <p head>)) @-}

data LL a = Nil | Cons a (LL a)

{-@ single :: a -> LL <{v:a| v >= head}> a @-}
single :: a -> LL a
single x = Cons x Nil 

