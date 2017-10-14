{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module AdtList where 

data LL a = Emp | Cons a (LL a) 

{-@ LIQUID "--exact-data-cons" @-}

{-@ test1 :: n:Int -> m:Int -> {v:() | Cons n (Cons m Emp) == Cons m (Cons n Emp)} -> {n == m} @-}
test1 :: Int -> Int -> () -> ()
test1 _ _ _ = ()


{-@ reflect sz @-}
sz :: LL a -> Int 
sz Emp = 0 
sz (Cons x xs) = 1 + sz xs

{-@ test2 :: () -> { sz (Cons 1 (Cons 2 Emp)) == 2 } @-}
test2 () = () 
