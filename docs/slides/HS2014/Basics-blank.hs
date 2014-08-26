{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diffcheck" @-}
{-@ LIQUID "--short-names" @-}
module Basics where

import           Data.List (find)




range lo hi
  | lo <= hi  = lo : range (lo + 1)  hi
  | otherwise = []

















rangeFind f lo hi = find f $ range lo hi



















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

range :: Int -> Int -> [Int]
