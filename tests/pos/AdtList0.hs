
{-@ LIQUID "--exact-data-cons" @-}

module AdtList0 where

data LL a = Emp | Cons a (LL a) 

{-@ test1 :: n:Int -> m:Int -> {v:() | Cons n (Cons m Emp) == Cons m (Cons n Emp)} -> {n == m} @-}
test1 :: Int -> Int -> () -> ()
test1 _ _ _ = ()

