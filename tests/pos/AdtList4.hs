-- | THIS FAILS because we don't support < and > for ADT and,
--   we instantiate the output of `app` with quals like `v < xs` `v > xs` etc.
--   where v, xs are of the ADT sort `List a`.

{-@ LIQUID "--exact-data-cons" @-}

module AdtList where 

data LL a = Emp | Cons a (LL a) 

{-@ data LL [sz] @-}

{-@ test1 :: n:Int -> m:Int -> {v:() | Cons n (Cons m Emp) == Cons m (Cons n Emp)} -> {n == m} @-}
test1 :: Int -> Int -> () -> ()
test1 _ _ _ = ()

{-@ app :: xs:LL a -> ys:LL a -> {v:LL a | sz v = sz xs + sz ys} @-} 
app = go 
  where 
    {-@ go :: xs:LL a -> ys:LL a -> {v:LL a | sz v = sz xs + sz ys} @-} 
    go Emp ys         = ys 
    go (Cons x xs) ys = Cons x (go xs ys)

{-@ measure sz @-}
{-@ sz :: LL a -> Nat @-}
sz :: LL a -> Int 
sz Emp         = 0 
sz (Cons x xs) = 1 + sz xs


