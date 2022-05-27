{-@ LIQUID "--max-case-expand=0" @-}
{-@ LIQUID "--exactdc" @-}

module T1267 where

data ABC = A | B | C 

foo :: Int -> ABC -> ()
foo 0 A  =  ()
foo x A | x /= 0 = ()
foo _ A = error " " 
foo _ t = ()
