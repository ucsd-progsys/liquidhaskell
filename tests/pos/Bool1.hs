module Bool1 where

{-@ baz :: x:Bool -> {v:Bool | v == x} @-}
baz :: Bool -> Bool 
baz x = x 
