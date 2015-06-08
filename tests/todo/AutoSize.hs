module AutoSize where

import GHC.Base

data List a = N | Cons a (List a) 


nil = N
cons = Cons 

{- foo :: xs:List a -> {v:Int | len xs = v} @-}
foo :: List a -> Int 
foo N = 0 
foo (Cons x xs) = 1 + foo xs 