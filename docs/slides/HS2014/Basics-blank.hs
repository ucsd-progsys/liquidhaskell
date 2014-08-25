{-@ LIQUID "--no-termination" @-}
module Basics where

import           Data.List (find)





































range lo hi
  | lo <= hi  = lo : range (lo + 1) hi
  | otherwise = []














rangeFind f lo hi = find f $ range lo hi






















append []     ys = ys
append (x:xs) ys = x : append xs ys



















data CSV a = CSV { cols :: [String], rows :: [[a]] }

good_csv = CSV [ "Month", "Days"]
               [ ["Jan",  "31"]
               , ["Feb",  "28"] 
               ]

bad_csv  = CSV [ "Month", "Days"]
               [ ["Jan",  "31"]
               , ["Feb"       ]
               ]
















-- Local Variables:
-- flycheck-checker: haskell-liquid
-- End:
