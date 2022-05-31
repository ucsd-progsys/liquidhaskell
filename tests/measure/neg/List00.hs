{-@ LIQUID "--expect-any-error" @-}
module List00 where

data List yy
  = Emp 
  | Cons yy (List yy)

{-@ measure kons @-}
kons :: List zoob -> Int 
kons Emp        = 0 
kons (Cons _ _) = 1 

{-@ foo :: l:List apple -> {v:Int | v = kons l} @-} 
foo :: List pig -> Int 
foo Emp        = 10 
foo (Cons _ _) = 1
