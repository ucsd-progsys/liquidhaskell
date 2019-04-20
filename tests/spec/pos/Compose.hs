{-@ incr :: x:_ -> {v:_ | v = x + 1} @-}
incr :: Int -> Int 
incr x = x + 1

{-@ incr2 :: x:_ -> {v:_ | v = x + 2} @-}
incr2 = incr . incr 

