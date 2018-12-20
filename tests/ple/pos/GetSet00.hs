{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module GetSet00 where 

type State = Int 

{-@ reflect set @-}
set :: State -> Int -> State 
set s x = x 

{-@ reflect get @-}
get :: State -> Int -> Int 
get s x = if x == s then 100 else 0 

{-@ ok :: s:State -> { get (set s 66) 66 == 100 } @-}
ok :: State -> () 
ok _ = ()

{-@ fails :: s:State -> { s1:State | get s1 77 == 100 } @-}
fails :: State -> State  
fails s = set s 77 

