{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module PLE where 

{-@ reflect adder @-}
adder :: Int -> Int -> Int 
adder x y = x + y 

{-@ prop :: { v : () | adder 5 6 == 12 } @-}
prop = ()
