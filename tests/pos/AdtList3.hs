{-@ LIQUID "--exact-data-cons" @-}

module AdtList where 

data LL a = Emp | Cons a (LL a) 

{-@ data LL [sz] @-}

{-@ test1 :: n:Int -> m:Int -> {v:() | Cons n (Cons m Emp) == Cons m (Cons n Emp)} -> {n == m} @-}
test1 :: Int -> Int -> () -> ()
test1 _ _ _ = ()

{-@ measure sz @-}
{-@ sz :: LL a -> Nat @-}
sz :: LL a -> Int 
sz Emp         = 0 
sz (Cons x xs) = 1 + sz xs


app :: LL a -> LL a -> LL a 
app Emp z         = z 
app (Cons x xs) z = Cons x (app xs z)
