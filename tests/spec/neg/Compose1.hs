{-@ incr :: x:_ -> {v:_ | v = x + 1} @-}
incr :: Int -> Int 
incr x = x + 1

-- override the input spec
{-@ assume GHC.Base.. :: (b -> c) -> (a -> b) -> a -> c @-}

-- so should not be able to prove the below
{-@ incr2 :: x:_ -> {v:_ | v = x + 2} @-}
incr2 = incr . incr 

