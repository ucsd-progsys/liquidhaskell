
{-@ LIQUID "--ple" @-}

import InfixLib 

-- GRRR...
{- infix +++ @-}

{-@ silly :: x:Int -> { x +++ 10 == x + 20} @-}
silly :: Int -> () 
silly _ = () 

