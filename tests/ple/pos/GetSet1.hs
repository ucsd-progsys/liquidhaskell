{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module GetSet1 where 

type State = [(Int,Int)]

{-@ reflect set @-}
set :: State -> Int -> Int -> State 
set s x v = (x, v) : s 

{-@ reflect get @-}
get :: State -> Int -> Int 
get []        y = 0 
get ((x,v):s) y = if x == y then v else get s y 

{-
{-@ ok :: s:State -> { get (set s 66 8000) 66 == 8000 } @-}
ok :: State -> () 
ok _ = ()
-}

{-@ fails :: s:State -> { s1:State | get s1 66 == 10 } @-}
fails :: State -> State  
fails s = set s 66 10

