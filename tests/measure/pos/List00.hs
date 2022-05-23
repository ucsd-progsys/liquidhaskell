module List00 where

import List00Lib

{-@ test :: {v:Int | v = 0 } @-}
test :: Int 
test = foo Emp 

{-@ bar :: l:List apple -> {v:Int | v = kons l} @-} 
bar :: List pig -> Int 
bar Emp        = 0 
bar (Cons _ _) = 1

imports = ( kons )
