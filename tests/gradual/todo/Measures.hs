-- | Sec 8 from Gradual Refinement Types 

module Measures where
{-@ LIQUID "--scrape-used-imports" @-}

-- This does not work because I need the special locality treatment for measures
{-@ f :: x:{v:[a] | ?? } -> {v:Int | ?? } -> a -> Bool @-}
f :: Eq a => [a] -> Int -> a -> Bool  
f xs i y= xs!!i == y 
