module Basics where

-- list of numbers between 0 and 100

list = [1,10,30]




















range :: Int -> Int -> [Int]
range lo hi
  | lo <= hi  = lo : range (lo + 1)  hi
  | otherwise = []

-- range 1 4 = [1,2,3]
-- range 1 1 = []










-- length (range lo hi) = hi - lo




























data CSV a = CSV { cols :: [String], rows :: [[a]] }

csv = CSV [ "Month", "Days"]
          [ ["Jan",  "31"]
          , ["Feb", "28"] 
          ]

















-- Local Variables:
-- flycheck-checker: haskell-liquid
-- End:

-- list :: [Int]

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diffcheck" @-}
{-@ LIQUID "--short-names" @-}
