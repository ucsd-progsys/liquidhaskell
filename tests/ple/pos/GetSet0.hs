{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module GetSet0 where 

type State = Int -> Int 

{-@ reflect set @-}
set :: State -> Int -> Int -> State 
set s x v y = if x == y then v else s y

{-@ reflect get @-}
get :: State -> Int -> Int 
get s x = s x 

{-@ ok :: s:State -> { get (set s 66 10) 66 == 10 } @-}
ok :: State -> () 
ok _ = ()

{-@ fails :: s:State -> { s1:State | get s1 66 == 10 } @-}
fails :: State -> State  
fails s = set s 66 10

