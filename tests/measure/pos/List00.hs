module List00 where 

data List a 
  = Emp 
  | Cons a (List a)

{-@ measure cons @-}
cons :: List a -> Int 
cons Emp        = 0 
cons (Cons _ _) = 1 

{-@ foo :: l:List a -> {v:Int | v = cons l} @-} 
foo :: List a -> Int 
foo Emp        = 0 
foo (Cons _ _) = 1
