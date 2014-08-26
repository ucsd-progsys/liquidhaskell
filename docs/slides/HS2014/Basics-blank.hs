{-@ LIQUID "--no-termination" @-}
{- LIQUID "--diffcheck" @-}
{-@ LIQUID "--short-names" @-}
module Basics where

import           Data.List (find)





































range lo hi
  | lo <= hi  = lo : range (lo + 1) hi
  | otherwise = []














rangeFind f lo hi = find f $ range lo hi






















append []     ys = ys
append (x:xs) ys = x : append xs ys



















data CSV a = CSV { cols :: [String], rows :: [[a]] }

csv = CSV [ "Month", "Days"]
          [ ["Jan",  "31"]
          , ["Feb",  "28"] 
          ]

















-- Local Variables:
-- flycheck-checker: haskell-liquid
-- End:
