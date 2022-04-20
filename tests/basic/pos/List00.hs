module List00 where

data List a = Emp 

{-@ foo :: List a -> { v : Int | 20 <= v } @-} 
foo :: List a -> Int 
foo Emp = 100 
