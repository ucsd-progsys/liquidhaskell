module List00 where 

data List yy
  = Emp 
  | Cons yy (List yy)

{-@ measure cons @-}
cons :: List zoob -> Int 
cons Emp        = 0 
cons (Cons _ _) = 1 

{-@ foo :: l:List apple -> {v:Int | v = cons l} @-} 
foo :: List pig -> Int 
foo Emp        = 0 
foo (Cons _ _) = 1
