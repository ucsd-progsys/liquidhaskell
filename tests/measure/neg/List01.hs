{-@ LIQUID "--expect-any-error" @-}
module List01 where

data List yy
  = Emp 
  | Cons yy (List yy)

{-@ measure size @-}
size :: List zoob -> Int 
size Emp         = 0 
size (Cons _ xs) = 1 + size xs 

{-@ append :: xs:List a -> ys: List a -> {v:List a | size v = size xs + size ys} @-}
append :: List a -> List a -> List a 
append Emp         ys = ys 
append (Cons x xs) ys = (append xs ys)
