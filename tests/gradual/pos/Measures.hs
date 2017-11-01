-- | Sec 8 from Gradual Refinement Types 

module Measures where
{-@ LIQUID "--scrape-used-imports" @-}
{-@ LIQUID "--eliminate=none"      @-}
{-@ LIQUID "--gdepth=2"            @-}

-- This does not work because I need the special locality treatment for measures
{-@ f :: xs:{[a] | ?? } -> i:{Int | ?? } -> a -> Bool @-}
f :: Eq a => [a] -> Int -> a -> Bool  
f xs i y= xs!!i == y 
