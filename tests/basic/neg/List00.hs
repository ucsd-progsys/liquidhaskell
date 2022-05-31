{-@ LIQUID "--expect-any-error" @-}
module List00 where

data List a = Emp 

{-@ foo :: List a -> { v : Int | 200 <= v } @-} 
foo :: List a -> Int 
foo Emp = 100 
