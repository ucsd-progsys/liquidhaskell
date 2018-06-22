
{-@ diverge :: Int -> {false} @-}
{-@ lazy diverge @-}
diverge :: Int -> Int 
diverge n = diverge n

{-@ one_eq_two :: { 1 == 2 } @-}
one_eq_two = diverge 0
