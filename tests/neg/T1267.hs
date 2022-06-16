{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--max-case-expand=0" @-}

module T1267 where

data ABC = A | B | C 

foo :: Int -> ABC -> ()
foo 0 A  =  ()
foo x A | x /= 0 = ()
foo _ A = error " " 
foo _ t = ()
