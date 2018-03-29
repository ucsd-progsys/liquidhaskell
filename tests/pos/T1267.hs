{-@ LIQUID "--no-case-expand" @-}
{-@ LIQUID "--exactdc" @-}

module NoCaseExpand where

data ABC = A | B | C 

foo :: Int -> ABC -> ()
foo 0 A  =  ()
foo x A | x /= 0 = ()
foo _ A = error " " 
foo _ t = ()
