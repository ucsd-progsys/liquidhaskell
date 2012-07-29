{-# LANGUAGE TypeOperators, FlexibleContexts #-}

-- Exhaustive test sets for proper sorting and stability of
-- optimal sorts

module Optimal where

import Control.Arrow
import Control.Monad

import Data.List
import Data.Function

import Data.Vector.Generic hiding (map, zip, concatMap, (++), replicate, foldM)

interleavings :: [a] -> [a] -> [[a]]
interleavings [       ] ys        =  [ys]
interleavings xs        [       ] =  [xs]
interleavings xs@(x:xt) ys@(y:yt) =  map (x:) (interleavings xt ys)
                                  ++ map (y:) (interleavings xs yt)

monotones :: Int -> Int -> [[Int]]
monotones k = atLeastOne 0
 where
 atLeastOne i 0 = [[]]
 atLeastOne i n = map (i:) $ picks i (n-1)
 picks _ 0             = [[]]
 picks i n | i >= k    = [replicate n k]
           | otherwise = map (i:) (picks i (n-1)) ++ atLeastOne (i+1) n


stability :: (Vector v (Int,Int)) => Int -> [v (Int, Int)]
stability n = concatMap ( map fromList
                        . foldM interleavings []
                        . groupBy ((==) `on` fst)
                        . flip zip [0..])
              $ monotones (n-2) n

sort2 :: (Vector v Int) => [v Int]
sort2 = map fromList $ permutations [0,1]

stability2 :: (Vector v (Int,Int)) => [v (Int, Int)]
stability2 = [fromList [(0, 0), (0, 1)]]

sort3 :: (Vector v Int) => [v Int]
sort3 = map fromList $ permutations [0..2]

{-
stability3 :: [UArr (Int :*: Int)]
stability3 = map toU [ [0:*:0, 0:*:1, 0:*:2]
                     , [0:*:0, 0:*:1, 1:*:2]
                     , [0:*:0, 1:*:2, 0:*:1]
                     , [1:*:2, 0:*:0, 0:*:1]
                     , [0:*:0, 1:*:1, 1:*:2]
                     , [1:*:1, 0:*:0, 1:*:2]
                     , [1:*:1, 1:*:2, 0:*:0]
                     ]
-}

sort4 :: (Vector v Int) => [v Int]
sort4 = map fromList $ permutations [0..3]

