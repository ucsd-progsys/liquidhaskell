module Fixme where

import Prelude hiding (repeat, filter)

-- Checking productivity
--  1. Leino : syntactically ignore checks in syntactically productive locations
--  PLUS  fivesUp

{-@ fivesUp :: n:Nat -> Int -> [Int] @-}
fivesUp :: Int -> Int -> [Int]
fivesUp n m | n == 0    = m : fivesUp 5 (m+1)
            | otherwise = fivesUp (n-1) (m+1)


-- VS : Mini-adga: check that recursive calls return codata with *smaller* size
-- MINUS : fivesUp
-- PLUS  : depth preserving functions

{-map :: f:(a -> b) -> xs:[a] -> {v : [a]| (len v) = (len xs)}
 -}
bar (x:xs) = x : map id xs 
