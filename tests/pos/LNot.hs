{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
module LNot where 
import Prelude  hiding (any, all, filter, nub, foldr, flip)



{-@  lemma_all_ex_not :: f:(a->Bool) -> ls:[a] -> { (bnot (any f ls)) == all (bnot . f) ls} @-}
lemma_all_ex_not :: (a->Bool) -> [a] -> ()
lemma_all_ex_not f [] = ()
lemma_all_ex_not f (x:xs) 
  | f x = lemma_all_ex_not f xs 
lemma_all_ex_not f (x:xs) 
  | (bnot . f) x = lemma_all_ex_not f xs 

{-@ reflect any @-}
any :: (a -> Bool) -> [a] -> Bool 
any _ []     = False 
any p (x:xs) = if p x then True else any p xs

{-@ reflect all @-}
all :: (a -> Bool) -> [a] -> Bool 
all _ []     = True 
all p (x:xs) = if p x then all p xs else False 

{-@ reflect bnot @-}
{-@ bnot :: x:Bool -> {v:Bool | v = not x} @-} 
bnot :: Bool -> Bool 
bnot True  = False 
bnot False = True  