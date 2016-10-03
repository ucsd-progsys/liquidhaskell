module TotalHaskell where

-- | totalHaskell overrides no-termination
-- | and checks for both totality & termination 

{-@ LIQUID "--total-Haskell"   @-}
{-@ LIQUID "--no-termination" @-}

fib :: Int -> Int 
fib 0 = 0 
fib 1 = 1 
fib i | 1 < i = fib i + fib (i-2)