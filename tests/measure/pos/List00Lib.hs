module List00Lib where

data List yy
  = Emp 
  | Cons yy (List yy)

{-@ measure kons @-}
kons :: List zoob -> Int 
kons Emp        = 0 
kons (Cons _ _) = 1 

{-@ foo :: l:List apple -> {v:Int | v = kons l} @-} 
foo :: List pig -> Int 
foo Emp        = 0 
foo (Cons _ _) = 1

