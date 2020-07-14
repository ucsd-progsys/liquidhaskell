{-@ LIQUID "--max-case-expand=0" @-}

module NoCaseExpand where

data ABC = A | B | C 

foo :: Int -> ABC -> ()
foo 0 A  =  ()
foo x A | x /= 0 = ()
foo _ A = error " " 
foo _ t = ()
