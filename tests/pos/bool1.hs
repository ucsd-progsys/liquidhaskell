module EqBool where 

{-@ baz :: x:Bool -> {v:Bool | v == x} @-}
baz :: Bool -> Bool 
baz x = x 
